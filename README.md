
## Requirements

This presentation package uses Harp to compile and serve your presentation.

You will need:
- Node >= 0.10
- NPM

To install Harp, which serves the presentation:

```
$ sudo npm install -g harp
```

## Configuration

Basic presentation configuration variables can be found in harp.js. This includes your project name, for example.

Slides can be edited directly in public/index.jade

## Authoring

To make authoring large presentations easier, slides are packaged into sections under the public/sections folder. Two sections are provided by default.

Adding or reordering sections can be done in sections/_data.js. The section file name should correspond to its key in that data file.

Individual sections are written using either Jade (as provided), EJS templates, or HTML. Jade has the advantage of being simple yet as powerful as regular HTML.

Markdown can be included in Jade by adding a :markdown section (though Jade is pretty simple by itself) e.g.

```
section
	:markdown
		## My Title
		
		Some content
```

## Running your presentation

To see your presentation, run the harp server.

```
$ harp server app
```

Your presentation should now be available at <a href="http://localhost:9000/">http://localhost:9000/</a>.

## Compiling to run without Harp

To compile your presentation down down standard HTML, CSS and JavaScript:

``` 
$ harp compile
```
