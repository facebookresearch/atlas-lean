# Abstract binding trees and alpha-equivalence

Fix a signature of operators, each with an arity specifying the number of arguments and, for each argument, the number of variables it binds. Abstract binding trees over the signature are built from variables and operator applications whose arguments are abstractions $x_1 \dots x_k . a$. The free variables of a tree are defined as usual, and *alpha-equivalence* is the least congruence identifying two abstractions that differ only by a consistent renaming of their bound variables to variables not free in the body. Operations on syntax, such as capture-avoiding substitution, are defined on alpha-equivalence classes.

## Sources

- R. Harper, *Practical Foundations for Programming Languages*, 2nd ed., Cambridge University Press, 2016
