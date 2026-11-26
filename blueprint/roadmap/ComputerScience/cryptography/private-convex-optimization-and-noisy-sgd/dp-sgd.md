# Differentially private stochastic gradient descent

Let $\mathcal{W} \subseteq \mathbb{R}^d$ be convex with diameter $D$, let $\ell(w, z)$ be convex and $L$-Lipschitz in $w$ for every data point $z$, let $\hat F_S(w) = \frac1n\sum_i \ell(w, z_i)$ be the empirical risk of a dataset $S$ and $F(w) = \mathbb{E}_{z \sim \mathcal{D}}[\ell(w,z)]$ the population risk. **DP-SGD** with clipping norm $C$, sampling rate $q$, noise multiplier $\sigma$, step sizes $\eta_t$ and $T$ steps does the following at each step $t$: form a random mini-batch $B_t$ by including each example independently with probability $q$; for each $i \in B_t$ compute the gradient $g_i = \nabla_w \ell(w_t, z_i)$ and clip it to $\bar g_i = g_i \min(1, C/\|g_i\|_2)$; set

$$
w_{t+1} = \Pi_{\mathcal{W}}\Big(w_t - \eta_t\, \frac{1}{qn}\Big(\sum_{i \in B_t} \bar g_i + \mathcal{N}(0, \sigma^2 C^2 I_d)\Big)\Big).
$$

Each step is a subsampled Gaussian mechanism with $\ell_2$-sensitivity $C$ for the sum of clipped gradients; the output (and every intermediate iterate) is released.

## Depends on

- [Private empirical risk minimization and private stochastic convex optimization](private-erm-and-sco.md)
- [The Gaussian mechanism](../differential-privacy/gaussian-mechanism-differentially-privat.md)

## Sources

- M. Abadi, A. Chu, I. Goodfellow, H. B. McMahan, I. Mironov, K. Talwar, L. Zhang, "Deep Learning with Differential Privacy", ACM CCS (2016), arXiv:1607.00133.
- R. Bassily, A. Smith, A. Thakurta, "Differentially Private Empirical Risk Minimization: Efficient Algorithms and Tight Error Bounds", FOCS (2014), arXiv:1405.7085.
