# Single instantiation for computations

If `c` has type `C` in `Γ` extended by an
innermost variable `x : A`, and `Γ ⊢ v : A`, then `Γ ⊢ c[v/x] : C`. This covers the steps for
application, `do` after `return`, and the return clause of a handler (Pretnar 2015, §3).
