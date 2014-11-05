var components = {
    "packages": [
        {
            "name": "revealjs",
            "main": "revealjs-built.js"
        }
    ],
    "shim": {
        "revealjs": {
            "exports": "Reveal"
        }
    },
    "baseUrl": "components"
};
if (typeof require !== "undefined" && require.config) {
    require.config(components);
} else {
    var require = components;
}
if (typeof exports !== "undefined" && typeof module !== "undefined") {
    module.exports = components;
}