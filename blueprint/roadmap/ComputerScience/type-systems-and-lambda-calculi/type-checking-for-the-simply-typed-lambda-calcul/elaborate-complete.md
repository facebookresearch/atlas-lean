# Completeness of elaboration

Assume equality of base types is decidable. If a raw term $r$
has type $A$ in context $\Gamma$ under the declarative typing judgment, then elaborating $r$ in
$\Gamma$ succeeds and returns the type $A$ together with some intrinsically typed term of type
$A$ in $\Gamma$.
