# Martingale representation of the Kaplan–Meier estimator

Let $\mathcal P_A(n) = \prod_{k<n}(1 - (A_{k+1} - A_k))$ be the discrete product integral, $S = \mathcal P_\alpha$ and $\hat S = \mathcal P_{\hat A}$ the Kaplan–Meier process, where $\hat A_n = \sum_{k<n} Y_{k+1}^{-1}(N_{k+1} - N_k)$ is the Nelson–Aalen process of real processes $N$ and $Y$. If no increment of $\alpha$ equals $1$ and $M_n = N_n - \sum_{k<n} Y_{k+1}(\alpha_{k+1} - \alpha_k)$, then pathwise, for every $n$,

$$\frac{\hat S_n}{S_n} - 1 = -\sum_{k<n} \frac{\hat S_k}{S_{k+1}}\, Y_{k+1}^{-1}\,(M_{k+1} - M_k) + \sum_{k<n} \frac{\hat S_k}{S_{k+1}}\, \mathbf 1\{Y_{k+1} = 0\}\,(\alpha_{k+1} - \alpha_k),$$

where $Y_{k+1}^{-1}$ is read as $0$ when $Y_{k+1} = 0$ (zero risk). The second sum is the vanishing-risk remainder; it is $0$ while the risk set is nonempty.
