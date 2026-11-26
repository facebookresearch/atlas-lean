# Class well-formedness

A class declaration is well formed (CLASS-OK) when field lookup for its superclass succeeds with some field list `fs`, its constructor parameters are exactly `fs` followed by its own fields, and every one of its methods is well formed (METHOD-OK).
