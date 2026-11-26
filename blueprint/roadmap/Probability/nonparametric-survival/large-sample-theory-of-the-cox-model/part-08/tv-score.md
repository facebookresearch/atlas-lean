# Scalar time-dependent Cox score

For a scalar covariate process, the time-dependent Cox score is $\sum_{i:\delta_i}(z_i(T_i) - \bar z_i(b))$, with $\bar z_i(b)$ the mean of the covariate values $z_l(T_i)$, evaluated at the event time $T_i$, over the risk set $R(T_i) = \{l : T_l \ge T_i\}$ (subjects tied with $i$ included), weighted by $e^{bz_l(T_i)}$.
