# Bernstein-type self-normalized bound for vector-valued martingales

If the noise is bounded by $R$ with conditional variance at most $\sigma^2$, the norm $\lVert\sum_i x_i\eta_i\rVert_{Z_t^{-1}}$ of the noise sum is at most $\beta_t = 8\sigma\sqrt{d\log(1+tL^2/(d\lambda))\log(4t^2/\delta)} + 4R\log(4t^2/\delta)$ for all $t$, with probability $1-\delta$: the leading term scales with $\sigma$, not $R$.

**Statement.** Let $(\mathcal{G}_t)_{t \ge 1}$ be a filtration and $(x_t, \eta_t)_{t \ge 1}$ a process with $x_t \in \mathbb{R}^d$ $\mathcal{G}_t$-measurable and $\eta_t \in \mathbb{R}$ $\mathcal{G}_{t+1}$-measurable. Fix $R, L, \sigma, \lambda > 0$ and $\mu^\ast \in \mathbb{R}^d$, let $y_t = \langle \mu^\ast, x_t \rangle + \eta_t$, and suppose that for all $t$

$$
|\eta_t| \le R, \qquad \mathbb{E}[\eta_t \mid \mathcal{G}_t] = 0, \qquad \mathbb{E}[\eta_t^2 \mid \mathcal{G}_t] \le \sigma^2, \qquad \lVert x_t \rVert_2 \le L .
$$

Put $Z_t = \lambda I + \sum_{i=1}^t x_i x_i^{\mathsf T}$, $b_t = \sum_{i=1}^t y_i x_i$, and let $\mu_t = Z_t^{-1} b_t$ be the ridge estimate for the rows $x_1^{\mathsf T}, \dots, x_t^{\mathsf T}$ and responses $y_1, \dots, y_t$. Let

$$
\beta_t = 8\sigma \sqrt{d \log\big(1 + tL^2/(d\lambda)\big) \log(4t^2/\delta)} + 4R \log(4t^2/\delta).
$$

Then for every $0 < \delta < 1$, with probability at least $1-\delta$, for all $t > 0$ simultaneously,

$$
\Big\lVert \sum_{i=1}^t x_i \eta_i \Big\rVert_{Z_t^{-1}} \le \beta_t, \qquad \lVert \mu_t - \mu^\ast \rVert_{Z_t} \le \beta_t + \sqrt\lambda\, \lVert \mu^\ast \rVert_2 .
$$

Compared with the [sub-Gaussian self-normalized bound](self-normalized-bound-for-vector-martingales.md), which with $R$-sub-Gaussian noise gives a radius of order $R\sqrt{d\log((1 + tL^2/\lambda)/\delta)}$, the dominant term here depends on the conditional standard deviation $\sigma$, while $R$ enters only through a lower-order logarithmic term. Applied to inputs divided by a per-round variance upper bound $\bar\sigma_t$ (weighted ridge regression), it handles heteroscedastic noise.

## Depends on

- [Filtrations and stopping times](../../../../Probability/martingales/stopping-times-and-martingale-problems/filtrations-and-stopping-times.md)
- [Conditional expectation given a σ-field](../../../../Probability/foundations/conditional-expectation/conditional-expectation-given-a-sigma-field/conditional-expectation.md)
- [Ridge estimate](../../supervised-learning/least-squares-ridge-and-lasso-regression/ridge-estimate.md)

## Proof depends on

- [Elliptical potential lemma](../multi-armed-bandits/elliptical-potential-lemma.md)

## Expansion

The source adapts the argument of Dani, Hayes and Kakade (2008). Write $d_t = \sum_{i \le t} x_i\eta_i$ and expand $\lVert d_t \rVert^2_{Z_t^{-1}}$ through the rank-one updates of $Z_t$. The increments are martingale differences in $\eta_i$ whose size is controlled by $\lVert x_i \rVert_{Z_{i-1}^{-1}}$ and by the running value of $\lVert d_{i-1} \rVert_{Z_{i-1}^{-1}}$. Freedman's inequality for real martingale differences (the source's Lemma B.1), with the conditional variance bound $\sigma^2$ and the range bound $R$, is applied to these increments multiplied by the indicator $E_{i-1}$ that the claimed bound held at all earlier rounds, with a union bound over $t$ (the $\log(4t^2/\delta)$ factor); an induction on $t$ then removes the indicators. The sum of the squared normalized inputs enters through $\sum_{t \le T} \min\{1, \lVert x_t \rVert^2_{Z_{t-1}^{-1}}\} \le 2d\log\big((d\lambda + TL^2)/(d\lambda)\big)$, the elliptical potential lemma. The second inequality follows from $\mu_t - \mu^\ast = Z_t^{-1}(d_t - \lambda\mu^\ast)$.

A complete expansion adds a page for Freedman's inequality for real-valued martingale differences on a general filtered probability space. For $x_i$ that are $\mathcal{G}_i$-measurable with $|x_i| \le M$, $\mathbb{E}[x_i \mid \mathcal{G}_{i-1}] = 0$ and predictable variation $\sum_{i \le n} \mathbb{E}[x_i^2 \mid \mathcal{G}_{i-1}] \le v$ almost surely, it gives, with probability at least $1-\delta$, $\sum_{i \le n} x_i \le \sqrt{2v\log(1/\delta)} + \tfrac23 M\log(1/\delta)$. The source's Lemma B.1 conditions the variance on $\mathcal{G}_i$ instead of $\mathcal{G}_{i-1}$. With $x_i$ $\mathcal{G}_i$-measurable that is the realized square $x_i^2$, but its proof applies the lemma to increments that are $\mathcal{G}_{i+1}$-measurable and centred given $\mathcal{G}_i$, which is the predictable form above with the index shifted.

## Sources

- D. Zhou, Q. Gu and Cs. Szepesvári, "Nearly Minimax Optimal Reinforcement Learning for Linear Mixture Markov Decision Processes", Conference on Learning Theory (COLT 2021), PMLR 134:4532–4576. Numbers from arXiv:2012.08507v2: Theorem 4.1 and the comparison after it, Appendix B.1 (proof, using Lemma B.1, Freedman's inequality, and Lemma B.2). <https://arxiv.org/abs/2012.08507v2>
