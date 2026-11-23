# Patterson Taylor Step

One step of Patterson's Taylor recursion (Theorem 7):
`f ↦ (x (1 - x) f(x) / 2)'' - f(x) / x`. In his Theorem 7, iterating this step `n`
times from `f₀ = f` and evaluating at the present frequency `y` gives the `n`-th
`t`-derivative at `t = 0` of `F(y, f; t) = ∫₀¹ f(x) C(x, y; t) dx`; that theorem
needs the killed density `C` and is not formalized here.
