# Score vector with time-dependent covariates

The score vector with time-dependent covariates is $\sum_{i:\delta_i}(x_i(T_i) - \bar x_i(\beta))$, with $\bar x_i(\beta)$ the $e^{\langle\beta, x_l(T_i)\rangle}$-weighted mean of the covariate values $x_l(T_i)$, evaluated at the event time $T_i$, over the risk set $R(T_i) = \{l : T_l \ge T_i\}$ (subjects tied with $i$ included).
