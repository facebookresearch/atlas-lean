# Terms of the calculus with exceptions

The terms are variables (de Bruijn indices),
abstractions `λ. b` whose body binds index `0`, applications, numerals, multiplication, the zero
test `ifz c t e` (which is `t` when `c` is `0` and `e` otherwise), `raise e`, and
`try e₁ with x. e₂`, written `tryWith e₁ e₂`, whose handler `e₂` binds index `0` to the raised
value.
