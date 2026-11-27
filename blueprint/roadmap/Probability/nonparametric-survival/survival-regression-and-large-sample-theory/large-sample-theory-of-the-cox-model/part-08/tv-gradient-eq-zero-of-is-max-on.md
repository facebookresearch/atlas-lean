# A time-dependent maximizer is a root of the score

For survival data with observed times $T_i$, event indicators $\delta_i$ and time-dependent covariates $x_i(t) \in \mathbb{R}^p$, let $\ell(\beta) = \sum_{i:\delta_i}\big(\langle\beta, x_i(T_i)\rangle - \log\sum_{l\in R(T_i)}e^{\langle\beta, x_l(T_i)\rangle}\big)$, where $R(T_i) = \{l : T_l \ge T_i\}$, with score vector $U$ and information matrix $I$. If $b$ maximizes $\ell$, then $U(b) = 0$.
