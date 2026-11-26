# Small-noise expansion of Muller's ratchet

**Model.** Let $X_k(t)$ be the frequency of individuals carrying $k = 0, 1, 2, \dots$ deleterious mutations, $\sum_k X_k = 1$, $X_{-1} := 0$. With selection coefficient $\alpha \ge 0$, unidirectional mutation rate $\lambda \ge 0$ and effective population size $\nu > 0$, the Fleming–Viot model of Muller's ratchet is
$$
dX_k = \Bigl(\alpha\Bigl(\sum_{j \ge 0} (j - k) X_j\Bigr) X_k + \lambda (X_{k-1} - X_k)\Bigr)dt + \sum_{\ell \ne k} \sqrt{\tfrac{1}{\nu} X_k X_\ell}\, dW_{k\ell},
$$
with independent Brownian motions $(W_{k\ell})_{k > \ell}$ and $W_{k\ell} = -W_{\ell k}$. Write $\theta = \lambda/\alpha$, $m_1(x) = \sum_k k x_k$ for the mean number of mutations, $g_\xi(x) = \sum_k x_k e^{-\xi k}$ for the generating function, and $\mathrm{Poi}(\theta)$ for the Poisson profile $x_k = e^{-\theta}\theta^k / k!$.

**Results.**
1. *(Well-posedness.)* For $x$ with $\sum_k x_k e^{\chi k} < \infty$ for some $\chi > 0$, the martingale problem is well posed; its solution has continuous paths and is the unique weak solution of the SDE started at $x$.
2. *(Deterministic limit, $\nu = \infty$.)* Started in $x$, the noiseless system has the explicit solution
$$
x_k(t) = \frac{e^{-\theta(1 - e^{-\alpha t})}}{g_{\alpha t}(x)} \sum_{i=0}^{k} x_i\, e^{-\alpha i t}\, \frac{\bigl(\theta(1 - e^{-\alpha t})\bigr)^{k-i}}{(k-i)!}.
$$
A Poisson profile stays Poisson: $\mathrm{Poi}(\varphi) \mapsto \mathrm{Poi}(\theta + (\varphi - \theta)e^{-\alpha t})$, so $\mathrm{Poi}(\theta)$ is the mutation–selection equilibrium.
3. *(First-order noise correction.)* If $X(0) = \mathrm{Poi}(\theta)$ and $\alpha, \lambda > 0$, $t \ge 0$ are fixed, then as $\nu \to \infty$
$$
\mathbb{E}\bigl[m_1(X(t))\bigr] = \theta + \frac{1}{2\nu\alpha}\Bigl(\exp\bigl(\theta(1 - e^{-\alpha t})^2\bigr) - 1\Bigr) + \mathcal{O}(\nu^{-2}),
$$
and an explicit $1/\nu$ expansion also holds for $\mathbb{E}[g_\xi(X(t)) g_\eta(X(t))]$ and for each $\mathbb{E}[X_k(t)]$.

## Depends on

- [Haldane–Muller load](../mutation-selection-balance/load-mult-at-equilibrium.md)

## Expansion

The generator splits as $G = G^{(1)} + G^{(2)}$: $G^{(1)}$ generates the deterministic mutation–selection flow, which acts on generating functions by $S_t g_\xi = g_{\xi + \alpha t} / g_{\alpha t} \cdot e^{-\theta(1 - e^{-\xi})(1 - e^{-\alpha t})}$, and $G^{(2)}$ is the neutral Fleming–Viot resampling operator with small coefficient $1/\nu$. Duhamel's formula $\mathbb{E}_x f(X_\tau) = S_\tau f(x) + \int_0^\tau \mathbb{E}_x G^{(2)} S_{\tau - s} f(X_s)\,ds$ applied once, with $X_s$ replaced by its deterministic Poisson path, gives the $1/\nu$ term; exponential-moment bounds on $m_1$ (a Gaussian tail $\exp(-2\alpha\nu c)$ for excursions above $\lambda\tau$) control the remainder. The positive correction to $\mathbb{E}\,m_1$ is the drift of the mutation load caused by random loss of the best class, i.e. the onset of clicks of the ratchet.

## Sources

- C. S. Heinzel, P. Pfaffelhuber, A. Wakolbinger, "A small noise approximation for Muller's Ratchet", arXiv:2606.15842 (2026), ratchet SDE of Section 1, Theorem 1.2, Corollary 1.3, Proposition 3.4, Theorem 3.5, Remark 3.8, Lemma 4.1, <https://doi.org/10.48550/arXiv.2606.15842>.
