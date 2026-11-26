# Coalescent limits of Pareto sampling with size-biasing

**Pareto sampling.** Let $X_1,\dots,X_N$ be i.i.d. Pareto$(\alpha)$, $\mathbf{P}(X_1 > x) = x^{-\alpha}$ for $x \ge 1$, $\alpha > 0$, with sum $\Sigma_N$, and set $S_n = X_n/\Sigma_N$. The pieces $S_n$ partition $[0,1]$ into the parents' shares of the next generation. A sample of $i$ individuals picks uniform points; individuals whose points hit the same piece share a parent. Size-biasing the whole generation by $\Sigma_N^\beta$ (for $\beta < \alpha$ such that $\mathbf{E}\Sigma_N^\beta < \infty$) gives the $i \to 1$ merger probability

$$ P^{(N)}_{i,1} = \frac{N\,\mathbf{E}\big(\Sigma_N^\beta S_1^i\big)}{\mathbf{E}\big(\Sigma_N^\beta\big)} \sim N\alpha\,\frac{\mathbf{E}\big(\Sigma_{N-1}^{\beta-\alpha}\big)}{\mathbf{E}\big(\Sigma_N^{\beta}\big)}\,\frac{\Gamma(i-\alpha)\Gamma(\alpha-\beta)}{\Gamma(i-\beta)}, \qquad i \ge 2,\ \beta < \alpha < 2, $$

where $\sim$ holds as $N \to \infty$: the right-hand form comes from dropping the constraint $X_1 \ge 1$ in the integral over $X_1$, so it is not exact at finite $N$ (at $N = 1$ the left side is $1$ and the right side is infinite). Analogous $i \to j$ transition probabilities define a discrete-time exchangeable coalescent. Let $c_N = P^{(N)}_{2,1}$ be the coalescence probability, and use the effective population size $N_e = c_N^{-1}$ as the time unit.

**Theorem (large-$N$ limits).**
1. $\alpha \in (0,1)$: without rescaling time, the coalescent converges to the discrete-time Poisson–Dirichlet$(\alpha,-\beta)$ $\Xi$-coalescent (simultaneous multiple mergers in each generation).
2. $\alpha \in (1,2)$: with $\mu = \alpha/(\alpha-1)$, $c_N \sim \alpha\mu^{-\alpha}B(2-\alpha,\alpha-\beta)N^{-(\alpha-1)}$, and on time scale $t/c_N$ the limit is the $\Lambda$-coalescent with $\Lambda = \mathrm{Beta}(2-\alpha,\alpha-\beta)$; for $\beta = 0$ this is the standard Beta$(2-\alpha,\alpha)$-coalescent.
3. $\alpha = 1$: $N_e = c_N^{-1} \sim \log N$, and the limit is the Beta$(1,1-\beta)$ $\Lambda$-coalescent, the Bolthausen–Sznitman coalescent when $\beta = 0$.
4. $\alpha = 2$: $c_N \sim \tfrac12\log N/N$, so $N_e = 2N/\log N$, and the limit is Kingman's coalescent.
5. $\alpha > 2$: with $\rho = \alpha/(\alpha-2)$, $N_e = N\mu^2/\rho$, and the limit is Kingman's coalescent.

**Forward-time interpretation.** These are the genealogies of a constant-size population with selection. Each individual of fitness $x$ produces offspring as a Poisson point process with power-law intensity scaled by $x$, and the $N$ fittest offspring survive. The offspring fitnesses then update multiplicatively as $x_n(k+1) \overset{d}{=} x_{N,\alpha}(k)\,x^*_{N+1}(k+1)\,X_n(k+1)$, where $x_{N,\alpha}(k) = (\sum_n x_n(k)^\alpha)^{1/\alpha}$ is the global equivalent fitness, $x^*_{N+1}$ has a power-gamma law, and the $X_n$ are Pareto$(\alpha)$. Backward in time, on the scale $c_N \sim 1/\log N$, the genealogy is the Beta$(1,1-\beta)$-coalescent.

## Depends on

- [Pitman's merger rate](../../coalescents/merger-rate.md)
- [Kingman's coalescent](../../coalescents/merger-rate-dirac-zero.md)
- [Merger rates of the Bolthausen–Sznitman coalescent](../../coalescents/merger-rate-volume.md)
- [The Beta-coalescent measure on the unit interval](../merger-rates-and-beta-coalescents/beta-lambda.md)
- [Merger rates of a coalescent with simultaneous multiple collisions](../../coalescents/xi-coalescents-simultaneous-multiple-collisions.md)

## Proof depends on

## Expansion

The tail index $\alpha$ of the offspring weights decides how often one parent captures a macroscopic fraction of the next generation. For $\alpha < 1$ the largest weight carries a positive fraction of $\Sigma_N$ already at finite $N$ (Poisson–Dirichlet ranked weights), so mergers occur in every generation. For $1 \le \alpha < 2$ the generalized central limit theorem ($\Sigma_N$ centered at $N\mu$ and scaled by $N^{1/\alpha}$, with a $\log N$ correction at $\alpha = 1$) makes single large families rare but non-negligible on the $N_e$ time scale, and their Beta-distributed sizes give the $\Lambda$-measure. For $\alpha \ge 2$ the weights have (borderline) finite variance, only pairwise mergers survive the time scaling, and Kingman's coalescent appears. The size-biasing exponent $\beta$ tilts the Beta parameters through the factor $\Gamma(\alpha-\beta)/\Gamma(i-\beta)$.

## Sources

- Thierry Huillet, "Pareto genealogies arising from a Poisson branching evolution model with selection", arXiv:1302.6029 (2013), Section 2 (Proposition 1), Section 3 (Theorem 2), Section 4 (Theorem 3, Lemma 4, Propositions 5–7, Lemma 8, Proposition 9), Section 5 (Propositions 10–12 and 17), <https://doi.org/10.48550/arXiv.1302.6029>; published in *Journal of Mathematical Biology* 68(3) (2014) 727–761, <https://doi.org/10.1007/s00285-013-0649-7>. Locators follow arXiv v1.
