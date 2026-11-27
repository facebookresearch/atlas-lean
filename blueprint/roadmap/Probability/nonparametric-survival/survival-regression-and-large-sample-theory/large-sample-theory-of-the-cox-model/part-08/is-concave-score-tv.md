# The scalar time-dependent log partial likelihood is a concave criterion

For survival data with a scalar time-dependent covariate $z_i(t)$, let $\ell(b)$ be the time-dependent log partial likelihood, $U(b) = \sum_{i:\delta_i}(z_i(T_i) - \bar z_i(b))$ its score and $I(b) = \sum_{i:\delta_i}\mathrm{Var}_i(b)$ its information, where $\bar z_i(b)$ and $\mathrm{Var}_i(b)$ are the $e^{bz_l(T_i)}$-weighted mean and variance of $z_l(T_i)$ over $R(T_i) = \{l : T_l \ge T_i\}$. Then $\ell' = U$, $U' = -I$ and $I \ge 0$.
