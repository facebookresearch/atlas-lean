# Differentially private stochastic gradient descent

Let $\mathcal{W} \subseteq \mathbb{R}^d$ be a nonempty, closed, convex set of finite diameter $D$, let $\ell(w, z)$ be convex and $L$-Lipschitz in $w$ for every data point $z$, let $\hat F_S(w) = \frac1n\sum_i \ell(w, z_i)$ be the empirical risk of a dataset $S$ and $F(w) = \mathbb{E}_{z \sim \mathcal{D}}[\ell(w,z)]$ the population risk, assumed finite (finiteness at one point implies it everywhere, by Lipschitzness). Since $\mathcal{W}$ is compact and both risks are continuous, their minima over $\mathcal{W}$ exist, and the Euclidean projection $\Pi_{\mathcal{W}}$ onto $\mathcal{W}$ is well defined. **DP-SGD** with clipping norm $C$, sampling rate $q$, lot size $m > 0$, noise multiplier $\sigma$, step sizes $\eta_t$ and $T$ steps does the following at each step $t$: form a random mini-batch $B_t$ by including each example independently with probability $q$; for each $i \in B_t$ compute the gradient $g_i = \nabla_w \ell(w_t, z_i)$ (for differentiable losses; otherwise a subgradient fixed by a data-independent rule) and clip it to $\bar g_i = g_i \min(1, C/\|g_i\|_2)$, with $\bar g_i = 0$ when $g_i = 0$; set

$$
w_{t+1} = \Pi_{\mathcal{W}}\Big(w_t - \eta_t\, \frac{1}{m}\Big(\sum_{i \in B_t} \bar g_i + \mathcal{N}(0, \sigma^2 C^2 I_d)\Big)\Big).
$$

Privacy is with respect to add/remove adjacency, as in Abadi et al.: neighbouring datasets differ by the presence of one example. The sampling rate $q$ and the lot size $m$ are public parameters, the same on neighbouring datasets; Abadi et al. (Algorithm 1) normalize by the lot size, written $L = qN$ there, and treat it and $q$ as fixed parameters. Normalizing by $qn$ for the actual dataset size $n$ would not be private, since $n$ differs between neighbours and would change the noise scale even when all gradients are zero. Under this adjacency the sum of clipped gradients has $\ell_2$-sensitivity $C$, so each step is a subsampled Gaussian mechanism with sensitivity $C$; under replace-one adjacency the sensitivity would be $2C$ (replacing a clipped gradient $Cu$ by $-Cu$ changes the sum by $2C$). The algorithm outputs the final iterate $w_T$. The privacy accounting covers the whole sequence of iterates, so releasing the transcript $w_1, \dots, w_T$ is an optional extension with the same guarantee, not part of the algorithm's output. The projection $\Pi_{\mathcal{W}}$ belongs to the constrained convex setting; Abadi et al. state the algorithm without it.

## Depends on

- [Private empirical risk minimization and private stochastic convex optimization](private-erm-and-sco.md)

## Sources

- M. Abadi, A. Chu, I. Goodfellow, H. B. McMahan, I. Mironov, K. Talwar, L. Zhang, "Deep Learning with Differential Privacy", ACM CCS (2016), arXiv:1607.00133, Section 2.1 and Algorithm 1.
- R. Bassily, A. Smith, A. Thakurta, "Differentially Private Empirical Risk Minimization: Efficient Algorithms and Tight Error Bounds", FOCS (2014), arXiv:1405.7085.
