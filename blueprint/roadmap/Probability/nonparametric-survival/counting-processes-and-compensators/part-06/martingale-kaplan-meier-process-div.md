# Kaplan–Meier martingale without vanishing risk

In discrete time, let $N$ and $Y$ be real processes and $\alpha$ a deterministic real sequence, with $Y$ predictable, $Y_0 \in \{0\} \cup [1, \infty)$ and $Y_{n+1} \ge 1$ for every $n$, such that $N - Y \bullet \alpha$ is a martingale, where $(Y \bullet \alpha)_n = \sum_{k<n} Y_{k+1}(\alpha_{k+1} - \alpha_k)$. No integer jumps are required of $N$; Aalen's model, with $N$ a counting process, $Y$ a number at risk and $\alpha$ a cumulative hazard, is the main application. Let $\hat A = Y^{-1} \bullet N$ be the Nelson–Aalen process (steps with $Y = 0$ contribute $0$). Let $\mathcal P_A(n) = \prod_{k<n}(1 - (A_{k+1} - A_k))$ be the discrete product integral, $S = \mathcal P_\alpha$ and $\hat S = \mathcal P_{\hat A}$ the Kaplan–Meier process. On a finite measure space, if $N$ is adapted, no increment of $\alpha$ equals $1$ and $0 \le N_{n+1} - N_n \le Y_{n+1}$ for every $n$, then $\hat S/S$ is a martingale.

## Sources

- R. D. Gill, "Censoring and Stochastic Integrals", Mathematical Centre Tracts 124, Amsterdam (1980).
