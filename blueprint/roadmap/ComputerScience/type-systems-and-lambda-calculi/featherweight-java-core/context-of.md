# Typing context of a method body

The typing context of a method of class `C` with parameter list `params` (pairs of a class and a variable name) gives `this` the type `C`; any other variable gets the class of the first parameter with that name, and a variable that is not a parameter is unbound. `this` takes priority, so a parameter named `this` is ignored, and of two parameters with the same name the first wins; there is no well-formedness premise. Used by the method typing rule (METHOD-OK).
