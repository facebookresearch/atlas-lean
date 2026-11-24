# Wright–Fisher diffusion with a strong seed bank

Fix a positive integer $c$ and $K \in (0, \infty)$, and let $(M_N)$ be positive integers with $N/M_N \to K$ as $N \to \infty$ (for example $M_N = \lceil N/K\rceil$). For each $N$ with $c \le \min(N, M_N)$ consider the Wright–Fisher model with a geometric seed bank of Blath, González Casanova, Kurt and Wilke-Berenguer (2016, Definition 2.1): $N$ active individuals and $M_N$ dormant ones, with $\varepsilon = c/N$ and $\delta_N = c/M_N$, so that $c$ individuals enter and $c$ leave the seed bank each generation. In each generation the active individuals produce $N - c$ active offspring by multinomial sampling, $c$ uniformly chosen dormant individuals become active and leave the seed bank, and the active individuals produce $c$ new dormant individuals by multinomial sampling; the other dormant individuals stay, and types are inherited. Let $X^N_k$ and $Y^N_k$ be the frequencies of one of two types among the active and the dormant individuals in generation $k$. Then:

1. For $f \in C^3([0, 1]^2)$ the rescaled one-step generators $A^Nf(x, y) = N\,\mathbb E_{x,y}[f(X^N_1, Y^N_1) - f(x, y)]$ converge pointwise on $[0, 1]^2$ to

    $$Af(x, y) = c(y - x)\,\partial_xf(x, y) + cK(x - y)\,\partial_yf(x, y) + \tfrac12x(1 - x)\,\partial_x^2f(x, y).$$

2. If $X^N_0 \to x$ and $Y^N_0 \to y$ almost surely, then $(X^N_{\lfloor Nt\rfloor}, Y^N_{\lfloor Nt\rfloor})_{t \ge 0}$ converges in distribution on $D_{[0,\infty)}([0, 1]^2)$ to the diffusion

    $$dX_t = c(Y_t - X_t)\,dt + \sqrt{X_t(1 - X_t)}\,dB_t, \qquad dY_t = cK(X_t - Y_t)\,dt,$$

    started at $(x, y)$, with $B$ a standard Brownian motion.

3. The limit is the moment dual of the block-counting process $(N_t, M_t)$ of the [seed-bank coalescent](seed-bank-coalescent-active-dormant-lineages.md), the Markov chain on $\mathbb N_0^2$ moving from $(n, m)$ to $(n - 1, m + 1)$ at rate $cn$, to $(n + 1, m - 1)$ at rate $cKm$ and to $(n - 1, m)$ at rate $\binom n2$: for all $x, y \in [0, 1]$, $n, m \in \mathbb N_0$ and $t \ge 0$, $\mathbb E_{x,y}[X_t^nY_t^m] = \mathbb E_{n,m}[x^{N_t}y^{M_t}]$.

The seed bank only exchanges genes with the active population, so genetic drift acts on the active frequency alone, and dormant lineages cannot coalesce, which is the rate structure of the dual.

## Depends on

- [Seed-bank coalescent](seed-bank-coalescent-active-dormant-lineages.md)

## Expansion

1. The one-step transition law as a sum over the hypergeometric number of germinating seeds of the type and two independent binomials (Proposition 2.2 of the source).
2. Moments of the one-step increments under the scaling $\varepsilon = c/N$, $\delta_N = c/M_N$ with $N\delta_N \to cK$, and the Taylor expansion giving the generator limit.
3. Tightness on the compact square and identification of the limit through the martingale problem for $A$, which is the generator of a Markov process.
4. The duality, from $Ax^ny^m$ being the dual generator applied to $(n, m) \mapsto x^ny^m$.

## Sources

- J. Blath, A. González Casanova, N. Kurt and M. Wilke-Berenguer, A new coalescent for seed-bank models, Ann. Appl. Probab. 26 (2016), 857–891, Section 2.1 (Definition 2.1, Propositions 2.2 and 2.4, Corollary 2.5) and Section 2.2 (Definition 2.7, Theorem 2.8). <https://arxiv.org/abs/1411.4747>
