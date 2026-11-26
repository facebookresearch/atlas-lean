# Method well-formedness

A method `m` of class declaration `cd`, with parameters, result class and body, is well formed (METHOD-OK) when its body has, under the context giving `this` the class of `cd` and each parameter its declared class, some type that is a subtype of the declared result class, and `m` passes the override check against the superclass of `cd` with its parameter classes and result class.
