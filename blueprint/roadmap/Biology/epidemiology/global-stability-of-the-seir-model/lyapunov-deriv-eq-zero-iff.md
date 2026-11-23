# The zero set of `V̇`

**The zero set of `V̇`** on the positive orthant is `{S = S*, E / E* = I / I*}`
(written `E I* = E* I`). It is a half-line through the equilibrium, not the equilibrium alone,
so `V̇ ≤ 0` does not by itself give convergence: the invariance step
(`IsSolution.tendsto_endemic`) shows that the only trajectory staying in this set is the
equilibrium.
