# Terms of the calculus with callcc

The terms are variables (de Bruijn indices),
abstractions `λ. b` whose body binds index `0`, applications, numerals, multiplication, the zero
test `ifz c t e` (which is `t` when `c` is `0` and `e` otherwise), `callcc e`, which calls the
value of `e` with the current continuation, and `abort e`, which replaces the whole program by
`e`.
