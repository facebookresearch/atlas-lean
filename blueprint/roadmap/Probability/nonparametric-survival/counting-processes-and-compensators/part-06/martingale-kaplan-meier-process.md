# Gill’s Kaplan–Meier martingale

In discrete time, let $N$ and $Y$ be real processes and $\alpha$ a deterministic real sequence, with $Y$ predictable and taking values in $\{0\} \cup [1, \infty)$, such that $N - Y \bullet \alpha$ is a martingale, where $(Y \bullet \alpha)_n = \sum_{k<n} Y_{k+1}(\alpha_{k+1} - \alpha_k)$. No integer jumps are required of $N$; Aalen's model, with $N$ a counting process, $Y$ a number at risk and $\alpha$ a cumulative hazard, is the main application. Let $\hat A = Y^{-1} \bullet N$ be the Nelson–Aalen process (steps with $Y = 0$ contribute $0$). Let $\mathcal P_A(n) = \prod_{k<n}(1 - (A_{k+1} - A_k))$ be the discrete product integral, $S = \mathcal P_\alpha$ and $\hat S = \mathcal P_{\hat A}$ the Kaplan–Meier process. If $N$ is adapted, no increment of $\alpha$ equals $1$ and $0 \le N_{n+1} - N_n \le Y_{n+1}$, then on a finite measure space the process

$$\frac{\hat S_n}{S_n} - 1 - \sum_{k<n} \frac{\hat S_k}{S_{k+1}}\, \mathbf 1\{Y_{k+1} = 0\}\,(\alpha_{k+1} - \alpha_k)$$

is a martingale: it equals $-\sum_{k<n} \frac{\hat S_k}{S_{k+1}} Y_{k+1}^{-1} (M_{k+1} - M_k)$ with $M = N - Y \bullet \alpha$, where $Y_{k+1}^{-1}$ is read as $0$ at zero risk.
