# Adjustment for the direct causes

**Adjustment for the direct causes** (Pearl 2009, Theorem 3.2.2; the case `Z = pa(X)` of
the back-door adjustment): for every function `f` of the variables,
`E[f | do(X_k = a)] = ∑_z P(pa_k = z) E[f | X_k = a, pa_k = z]`, assuming
`P(X_k = a, pa_k = z) > 0` whenever `P(pa_k = z) > 0`.
