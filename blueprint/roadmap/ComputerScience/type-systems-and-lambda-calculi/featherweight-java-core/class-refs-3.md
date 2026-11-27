# Class names referenced by a class declaration

The class names that a Featherweight Java class declaration refers to form a list, with repeats kept: its superclass, then the classes of its fields in order, then the classes of its constructor parameters in order, then, for each method in order, its return class, its parameter classes in order and the [class names of its body](class-refs.md). The list is used by the well-formedness check that every referenced class is declared or is the root class.
