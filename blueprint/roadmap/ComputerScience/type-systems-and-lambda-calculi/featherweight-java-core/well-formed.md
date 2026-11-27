# Well-formed class tables

A class table is well formed when:

- no declared class is named `Object`;
- the declared class names are distinct;
- every class named in a declaration (its superclass, the types of its fields and constructor parameters, the parameter and return types of its methods, and the classes in method bodies) is `Object` or a declared class;
- the chain of superclasses of every declared class has no repetition, so the class hierarchy is acyclic;
- the method names of each class are distinct;
- the field names of every class, inherited fields included, are distinct;
- every method declaration correctly overrides: if a superclass already has a method of that name, its parameter types and return type are those of the declaration;
- the parameters of every method are distinct and differ from `this`.
