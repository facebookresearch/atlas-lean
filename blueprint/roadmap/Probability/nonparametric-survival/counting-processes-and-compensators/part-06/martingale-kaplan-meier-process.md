# Gill’s Kaplan–Meier martingale

Consider Aalen's model in discrete time: a counting process $N$, a predictable at-risk process $Y$ with values in $\{0\} \cup [1, \infty)$ and a deterministic cumulative hazard $\alpha$, such that $N - Y \bullet \alpha$ is a martingale, with $\hat A = Y^{-1} \bullet N$ the Nelson–Aalen process (steps with $Y = 0$ contribute $0$). Let $\mathcal P_A(n) = \prod_{k<n}(1 - (A_{k+1} - A_k))$ be the discrete product integral, $S = \mathcal P_\alpha$ and $\hat S = \mathcal P_{\hat A}$ the Kaplan–Meier process. If $N$ is adapted, no increment of $\alpha$ equals $1$ and $0 \le N_{n+1} - N_n \le Y_{n+1}$, then on a finite measure space the process

$$\frac{\hat S_n}{S_n} - 1 - \sum_{k<n} \frac{\hat S_k}{S_{k+1}}\, \mathbf 1\{Y_{k+1} = 0\}\,(\alpha_{k+1} - \alpha_k)$$

is a martingale: it equals $-\sum_{k<n} \frac{\hat S_k}{S_{k+1}} Y_{k+1}^{-1} (M_{k+1} - M_k)$ with $M = N - Y \bullet \alpha$, where $Y_{k+1}^{-1}$ is read as $0$ at zero risk.
