# Phase transition of the noisy K-branching random walk fitness wave

**Model.** Fix $\beta > 0$ and $\gamma \in (0,1)$. A population of $K = \lfloor N^\gamma \rfloor$ individuals carries real fitnesses. Each generation every individual produces $m_N = N/K$ offspring whose fitness is the parent's plus an i.i.d. increment with law $F_X$; then $K$ offspring are sampled to form the next generation, with probability proportional to the Gibbs weight $e^{\beta_N x}$, $\beta_N = \beta \log N / c_N$, where $c_N = \inf\{x : 1 - F_X(x) \ge 1/N\}$. Assume exponential tails: $\log(1 - F_X(x c_N))/\log N \to -x$ for $x \ge 0$ (the case $\rho = 1$), with a comparable or lighter left tail.

**Log-profile dynamics.** If the rescaled configuration has a limiting log-profile $g^t$ (about $N^{g^t(x)}\,dx$ individuals near $x c_N$), then $g^{t+1} = s_{\sigma_t} \circ r(g^t)$, where with $\pi(x) = x$ for $x \ge 0$ and $-\infty$ otherwise,

$$r(g)(x) = \pi\Bigl(\sup_z \bigl(1 - \gamma + g(z) + h(x - z)\bigr)\Bigr), \qquad s_\sigma(g)(x) = \pi\bigl(g(x) + \beta (x - \sigma)_-\bigr),$$

$h(y) = -y$ for $y \ge 0$, and $\sigma_t = \inf\{\sigma : \sup_z s_\sigma(r(g^t))(z) \le \gamma\}$.

**Theorem.** This system has a unique travelling wave $G$ with speed $\nu(\gamma, \beta)$. Let $k = \lfloor 1/\beta \rfloor$ if $1/\beta \notin \mathbb N$ and $k = 1/\beta - 1$ otherwise, and

$$\gamma_c(\beta) = \frac{k\,(2 - (k+1)\beta)}{(k+1)(2 - k\beta)} .$$

- *Selection of the luckiest* ($\gamma < \gamma_c$): $\nu = \dfrac{2\gamma}{k\,(2 - (k+1)\beta)}$, increasing in $\gamma$; at the wave, every survivor is strictly fewer than the offspring produced at its fitness, i.e. $r(G)(x) > g^1(x)$ on the support.
- *Selection of the fittest* ($\gamma \ge \gamma_c$): $\nu = 1 - \gamma$, decreasing in $\gamma$; the top of the wave survives selection intact on $[-\chi + 1 - \gamma, 1 - \gamma]$, where $\chi = \gamma - \sum_{j=1}^{k} (1 - j\beta)(1 - \gamma) > 0$.

Under $\gamma \ne \gamma_c$ (and $1/\beta \notin \mathbb N$ when $\gamma > \gamma_c$) the travelling wave is locally stable.

## Expansion

The stochastic Hopf–Cole transform $\log(\text{count})/\log N$ turns the random particle system into deterministic max-plus operations: reproduction is a sup-convolution with the tail exponent $h$ and adds $\log m_N/\log N = 1 - \gamma$, while Gibbs selection tilts by $\beta x$ below a threshold $\sigma$ chosen so the population returns to size $N^\gamma$. For exponential tails the profiles become piecewise linear after finitely many steps, and the travelling wave is a staircase of $k+1$ linear pieces. When selection is weak (large $\gamma$) the leader's own offspring set the pace and the wave moves at $1-\gamma$; when selection is strong the wave is driven by rare large increments in the bulk, and the speed grows with $\gamma$, so wave speed is non-monotone in selection pressure.

## Sources

- "$K$-Branching Random Walk with Noisy Selection: Large Population Limits and Phase Transitions", arXiv:2509.26254 (2025), Theorems 3, 4 and 5 and Proposition 35, <https://doi.org/10.48550/arXiv.2509.26254>.
