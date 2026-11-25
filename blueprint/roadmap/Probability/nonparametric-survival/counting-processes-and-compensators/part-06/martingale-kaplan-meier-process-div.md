# Kaplan–Meier martingale without vanishing risk

Consider Aalen's model in discrete time: a counting process $N$, a predictable at-risk process $Y$ with values in $\{0\} \cup [1, \infty)$ and a deterministic cumulative hazard $\alpha$, such that $N - Y \bullet \alpha$ is a martingale, with $\hat A = Y^{-1} \bullet N$ the Nelson–Aalen process (steps with $Y = 0$ contribute $0$) and $\Lambda^* = \mathbf 1\{Y \ne 0\} \bullet \alpha$ the restricted hazard. Let $\mathcal P_A(n) = \prod_{k<n}(1 - (A_{k+1} - A_k))$ be the discrete product integral, $S = \mathcal P_\alpha$ and $\hat S = \mathcal P_{\hat A}$ the Kaplan–Meier process. On a finite measure space, if $N$ is adapted, no increment of $\alpha$ equals $1$, $0 \le N_{n+1} - N_n \le Y_{n+1}$ and the risk set never empties, then $\hat S/S$ is a martingale.

## Sources

- R. D. Gill, "Censoring and Stochastic Integrals", Mathematical Centre Tracts 124, Amsterdam (1980).
