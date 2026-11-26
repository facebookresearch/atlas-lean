# Information matrix with time-dependent covariates

For observed times $T_i$, event indicators $\delta_i$ and time-dependent covariates $x_l(t) \in \mathbb{R}^p$, the observed information matrix is $I(\beta) = \sum_{i:\delta_i}\mathrm{Cov}_i(\beta)$, where $\mathrm{Cov}_i(\beta)$ is the covariance matrix of the covariate values $x_l(T_i)$, evaluated at the event time $T_i$, over the risk set $R(T_i) = \{l : T_l \ge T_i\}$ (subjects tied with $i$ included), weighted by $e^{\langle\beta, x_l(T_i)\rangle}$.
