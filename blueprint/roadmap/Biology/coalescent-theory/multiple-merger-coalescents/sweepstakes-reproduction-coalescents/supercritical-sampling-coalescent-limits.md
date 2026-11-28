# Coalescent limits of supercritical sampling with heavy-tailed potential offspring

**Model (Schweinsberg's supercritical sampling).** A haploid panmictic population of constant size $N$ evolves in discrete, non-overlapping generations. In each generation the $N$ current individuals independently produce i.i.d. numbers $X_1, \dots, X_N$ of *potential offspring*, with $S_N = X_1 + \cdots + X_N$. If $S_N \ge N$, then $N$ of the potential offspring are sampled uniformly without replacement to form the next generation (the case $S_N < N$ has probability tending to $0$ when $\mathbb{E}X_1 > 1$). Let $c_N$ be the probability that two given gene copies of the same generation derive from the same parent, and let $\xi^{n,N}$ be the ancestral process of a sample of $n$ gene copies, valued in partitions of $[n]$. Assume $\mathbb{E}X_1 > 1$ and, for fixed $\alpha, C > 0$,

$$\lim_{x \to \infty} x^{\alpha}\, \mathbb{P}(X_1 \ge x) = C .$$

**Theorem.** $\{\xi^{n,N}(\lfloor t / c_N \rfloor);\, t \ge 0\}$ converges in finite-dimensional distributions to
1. the Kingman coalescent if $\alpha \ge 2$;
2. the Beta$(2-\alpha, \alpha)$-coalescent, the $\Lambda$-coalescent with $\Lambda(dx) = B(2-\alpha,\alpha)^{-1} x^{1-\alpha}(1-x)^{\alpha-1}\,dx$ on $(0,1]$, if $1 \le \alpha < 2$;
3. the Poisson–Dirichlet$(\alpha, 0)$-coalescent, a $\Xi$-coalescent with simultaneous multiple mergers, if $0 < \alpha < 1$; from $b$ blocks, a given collision of $r$ groups of sizes $k_1, \dots, k_r \ge 2$ with $s = b - \sum_i k_i$ untouched blocks has probability

$$p_{b;k_1,\dots,k_r;s} = \frac{\alpha^{r+s-1}(r+s-1)!}{(b-1)!} \prod_{i=1}^{r} (k_i - 1 - \alpha)_{k_i - 1},$$

where $(x)_m = x(x-1)\cdots(x-m+1)$, so $(k_i - 1 - \alpha)_{k_i - 1} = (1-\alpha)(2-\alpha)\cdots(k_i-1-\alpha)$ and $p_{2;2;0} = 1-\alpha$ (in this case the time scale is discrete, $c_N$ stays bounded away from $0$).

The coalescence probability has the asymptotics

$$\frac{1}{c_N} \asymp \begin{cases} 1, & 0 < \alpha < 1,\\ \log N, & \alpha = 1,\\ N^{\alpha-1}, & 1 < \alpha < 2,\\ N/\log N, & \alpha = 2,\\ N, & \alpha > 2, \end{cases} \qquad c_N \sim N\, \mathbb{E}\!\left[\frac{(X_1)_2}{S_N^2}\, \mathbf{1}\{S_N \ge N\}\right].$$

## Depends on

- [Cannings model of a haploid population](../cannings-models/cannings-model.md)
- [Closed form of the Beta-coalescent rates](../merger-rates-and-beta-coalescents/merger-rate-beta-lambda.md)

## Proof idea

Conditional on $(X_1, \dots, X_N)$ the offspring numbers $\nu_i$ are multivariate hypergeometric, so the probability that given groups of $k_1, \dots, k_r$ lineages merge is $\mathbb{E}[(\nu_1)_{k_1}\cdots(\nu_r)_{k_r}]/N^{\sum k_i - r} \sim N^r\, \mathbb{E}[(X_1)_{k_1}\cdots(X_r)_{k_r} S_N^{-\sum k_i}\mathbf{1}\{S_N \ge N\}]$. With $\alpha < 2$ one family can make a macroscopic fraction $X_1/S_N \approx X_1/(X_1 + N m)$ of the next generation; the tail $x^{-\alpha}$ of $X_1$ transported through $x \mapsto x/(x + Nm)$ produces the Beta$(2-\alpha,\alpha)$ density, and Möhle–Sagitov / Schweinsberg convergence criteria give the limit. For $\alpha < 1$, $S_N$ itself is dominated by its largest summands, the normalized order statistics are Poisson–Dirichlet$(\alpha,0)$, and several large families form in one generation, giving simultaneous mergers.

## Sources

- J. Schweinsberg, "Coalescent processes obtained from supercritical Galton–Watson processes", Stochastic Processes and their Applications 106 (2003), Theorem 4 and Lemmas 6, 13, 16, <https://doi.org/10.1016/S0304-4149(03)00028-0>.
- B. Eldon, "Gene genealogies in haploid populations evolving according to sweepstakes reproduction", Bulletin of Mathematical Biology 88 (2026), article 166, <https://doi.org/10.1007/s11538-026-01736-x>. Numbering as in the preprint arXiv:2601.09537v2, <https://arxiv.org/abs/2601.09537v2>: Definition 2.6 and Eq. (12) (the Poisson–Dirichlet$(\alpha,0)$ transition probability, which corrects the form quoted in its Remark 2.7), Theorem 2.9 and Eqs. (15)–(16).
