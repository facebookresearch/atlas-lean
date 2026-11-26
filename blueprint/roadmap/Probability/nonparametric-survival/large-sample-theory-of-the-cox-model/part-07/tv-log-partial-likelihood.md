# Log partial likelihood with time-dependent covariates

The log partial likelihood with time-dependent covariates is $\sum_{i:\delta_i}\big(\langle\beta, x_i(T_i)\rangle - \log\sum_{l\in R(T_i)}e^{\langle\beta, x_l(T_i)\rangle}\big)$, with risk set $R(T_i) = \{l : T_l \ge T_i\}$.
