# The remainder is the mean bias of the Kaplan–Meier ratio

Consider Aalen's model in discrete time with an adapted counting process $N$, a predictable at-risk process $Y \in \{0\} \cup [1, \infty)$, deaths $0 \le \Delta N \le Y$, no hazard increment $\Delta\alpha_k$ equal to $1$, and $N - Y\bullet\alpha$ a martingale; $\hat S$ the Kaplan–Meier process, $S = \prod(1 - \Delta\alpha)$ and $R_n = \sum_{k<n}\hat S_k/S_{k+1}\mathbf 1\{Y_{k+1} = 0\}\Delta\alpha_{k+1}$ the vanishing-risk remainder. On a finite measure space, for every $n$, $\mathbb{E}[\hat S_n/S_n - 1] = \mathbb{E}[R_n]$.
