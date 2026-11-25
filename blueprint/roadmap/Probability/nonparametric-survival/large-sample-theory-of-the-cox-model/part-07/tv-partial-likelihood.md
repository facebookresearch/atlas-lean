# Partial likelihood with time-dependent covariates

Cox's partial likelihood with time-dependent covariates is $\prod_{i:\delta_i}e^{\langle\beta, x_i(T_i)\rangle}/\sum_{l\in R(T_i)}e^{\langle\beta, x_l(T_i)\rangle}$, with risk set $R(T_i) = \{l : T_l \ge T_i\}$; since $i \in R(T_i)$, each denominator is positive.
