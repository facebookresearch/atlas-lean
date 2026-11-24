# Radiator solution exists trapped

Existence of the trapped physical solution: for every
`T0 ∈ [Tmin, Tmax]` there is a global trajectory `T` with
`T 0 = T0`, solving the clipped field everywhere
(`HasDerivAt T (clippedRadiatorRate ... (T t)) t` for all `t`),
staying in the box for all `t ≥ 0`, and there solving the
original field (`HasDerivAt T (radiatorRate ... (T t)) t`).
Existence uses the global existence theorem for globally
Lipschitz fields (`ode_global_exists_of_global_lipschitz`) with
the Lipschitz constant from `clippedRadiatorRate_lipschitz`.
