# Typing judgment of the calculus with exceptions

For a fixed exception type `exn`, the
judgment `HasType exn Γ e A`, where the context `Γ` lists the types of the free de Bruijn
variables (index `0` first), is the least relation closed under the rules of the simply typed
λ-calculus with natural numbers (multiplication of two numbers is a number; the zero test takes
a number and two branches of a common type) and the two exception rules: if `e` has type `exn`
then `raise e` has every type (Harper, rule 29.4a); if `e₁` has type `A` and `e₂` has type `A`
in `Γ` extended by a variable of type `exn`, then `try e₁ with x. e₂` has type `A` (Harper, rule
29.4b).
