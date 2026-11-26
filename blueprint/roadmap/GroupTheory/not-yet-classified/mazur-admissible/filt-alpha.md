# Number of steps tagged true

The number of steps of an admissible chain whose tag is `true`.
Only tags are counted: a step tagged `false` is cyclotomic, and for `p = 2` its quotient also has
trivial action (the mod-`2` cyclotomic character is trivial), but it is not counted. So
`filtAlpha c` depends on the tags chosen in `c`. It is the Galois-module counterpart of Mazur's
invariant `α`, the number of quotients `ℤ/p` in an admissible filtration.
