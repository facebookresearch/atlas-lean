# Replicable bounded-mean and coin-bias estimation

Let $X$ be any set, $\varphi : X \to [0, 1]$, and $\tau, \delta, \rho \in [0, 1]$ with $\rho > 2\delta$. The algorithm rSTAT sets $\alpha = 2\tau/(\rho + 1 - 2\delta)$, draws a shared offset $\alpha_{\mathrm{off}}$ uniformly from $[0, \alpha]$, splits $[0, 1]$ into the regions $[0, \alpha_{\mathrm{off}}), [\alpha_{\mathrm{off}}, \alpha_{\mathrm{off}} + \alpha), \dots, [\alpha_{\mathrm{off}} + i\alpha, \alpha_{\mathrm{off}} + (i+1)\alpha), \dots$ (the last region ending at $1$), computes the empirical mean $v$ of $\varphi$ on its sample, and returns the midpoint of the region containing $v$. From a sample of size $\tilde O\big(1/(\tau^2(\rho - 2\delta)^2)\big)$ drawn i.i.d. from any distribution $D$ on $X$, it is $\rho$-replicable and returns a value within $\tau$ of $\mathbb{E}_{x \sim D}\varphi(x)$ except with probability $\delta$ (Impagliazzo, Lei, Pitassi and Sorrell, Algorithm 1 and Theorem 2.3). Since this holds for every $D$, rSTAT is strongly $\rho$-replicable and a $(\tau, \delta)$-estimator of the mean of $\varphi$; with $\varphi$ the indicator of $\text{true}$, it estimates the bias $\Pr_D[\text{true}]$ of a coin $D$ on $\{\text{true}, \text{false}\}$.

## Proof sketch

A Chernoff bound puts each empirical mean within $\tau' = \tau(\rho - 2\delta)/(\rho + 1 - 2\delta)$ of the mean except with probability $\delta$, and the midpoint moves the estimate by at most $\alpha/2$, for a total error at most $\tau$. Two runs with the same offset return different values only if a region endpoint falls between their empirical means, which happens with probability at most $2\tau'/\alpha = \rho - 2\delta$ when both means are accurate; adding the $2\delta$ failure probability gives $\rho$ (proof of Theorem 2.3).

Derived (not stated in the cited source): for $f : X \to [a, b]$, apply rSTAT to $(f - a)/(b - a)$ and rescale; for every $\varepsilon, \rho, \beta > 0$, taking $\tau = \varepsilon$ and $\delta = \min(\beta, \rho/3)$ gives a strongly $\rho$-replicable $(\varepsilon, \beta)$-estimator. The same holds with a grid of width $w$ shifted by $iw/N$, $i$ uniform in $\{0, \dots, N-1\}$: by Hoeffding's inequality two independent empirical means are within $2t$ of each other except with probability $4e^{-2mt^2/(b-a)^2}$, the discrete rounding lemma bounds the disagreement by $2t/w + 1/N$ plus that probability, and rounding moves the estimate by at most $w/2$; choose $w = \varepsilon$, $t \le \varepsilon/2$ with $2t/w \le \rho/3$, $N \ge 3/\rho$, and $m$ with $4e^{-2mt^2/(b-a)^2} \le \min(\rho/3, \beta)$.

## Depends on

- [Replicable algorithms with shared randomness](replicable-algorithms-with-shared-seed.md)
- [Two-sided Hoeffding inequality for averages of bounded variables](../../../../Probability/concentration-inequalities/hoeffding-s-inequality/measure-real-abs-avg-sub-ge-le.md)

## Proof depends on

- [Randomized-threshold and random-grid rounding lemmas](randomized-rounding-disagreement.md)

## Sources

- R. Impagliazzo, R. Lei, T. Pitassi and J. Sorrell, "Reproducibility in Learning", Proceedings of the 54th Annual ACM SIGACT Symposium on Theory of Computing (STOC), 2022, Section 2, Algorithm 1 and Theorem 2.3; open copy: <https://arxiv.org/abs/2201.08430>.
- W. Hoeffding, "Probability Inequalities for Sums of Bounded Random Variables", Journal of the American Statistical Association, 1963.
