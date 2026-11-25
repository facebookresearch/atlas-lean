# The Kaplan–Meier remainder is positive after censoring

Consider Aalen's model in discrete time with a predictable at-risk process $Y \in \{0\} \cup [1, \infty)$, deaths $0 \le \Delta N \le Y$, hazard increments in $[0, 1)$, $\hat S$ the Kaplan–Meier process, $S = \prod(1 - \Delta\alpha)$ and $R_n = \sum_{k<n}\hat S_k/S_{k+1}\mathbf 1\{Y_{k+1} = 0\}\Delta\alpha_{k+1}$ the vanishing-risk remainder. If at some step $k < n$ the risk set is empty while $\hat S_k > 0$ and $\Delta\alpha_{k+1} > 0$, then $R_n > 0$.
