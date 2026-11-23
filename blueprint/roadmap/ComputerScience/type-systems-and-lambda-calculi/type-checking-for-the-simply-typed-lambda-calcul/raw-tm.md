# Raw lambda terms

Raw terms are extrinsic de Bruijn syntax over a given type of base
types: a raw term is either a variable given by a natural-number index $n$, an application
$f\,a$ of two raw terms $f$ and $a$, or a lambda abstraction $\lambda A.\,t$ consisting of a
simple type $A$ over the base types (the parameter type) and a raw term $t$ (the body).
Variables and applications carry no type information.
