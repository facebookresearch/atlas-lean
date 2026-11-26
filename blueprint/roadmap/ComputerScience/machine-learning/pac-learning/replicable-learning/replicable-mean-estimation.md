# Replicable bounded-mean and coin-bias estimation

Let $X$ be any set and $f : X \to [a, b]$. For every $\varepsilon, \rho, \beta > 0$ there are a grid width $w > 0$ and integers $N, m \ge 1$ such that the algorithm that computes the empirical mean of $f$ on $m$ i.i.d. samples and applies random grid rounding of width $w$ with a shared shift in $\{0, \dots, N-1\}$ is strongly $\rho$-replicable and an $(\varepsilon, \beta)$-estimator of $\mathbb{E}_{x \sim D} f(x)$ for every distribution $D$ on $X$. In particular the bias $\Pr_D[\text{true}]$ of a coin $D$ on $\{\text{true}, \text{false}\}$ has a strongly $\rho$-replicable $(\varepsilon, \beta)$-estimator.

## Proof sketch

By Hoeffding's inequality two independent empirical means are within $t$ of the mean, hence within $2t$ of each other, except with probability $4e^{-2mt^2/(b-a)^2}$. The rounding lemma bounds the disagreement by $2t/w + 1/N$ plus that failure probability, and rounding moves the estimate by at most $w/2$; choose $w = \varepsilon$ and $t \le \varepsilon/2$ with $2t/w \le \rho/3$, then $N \ge 3/\rho$ and $m$ large enough that $4e^{-2mt^2/(b-a)^2} \le \min(\rho/3, \beta)$.

## Depends on

- [Replicable algorithms with shared randomness](replicable-algorithms-with-shared-seed.md)
- [Two-sided Hoeffding inequality for averages of bounded variables](../../../../Probability/concentration-inequalities/hoeffding-s-inequality/measure-real-abs-avg-sub-ge-le.md)

## Proof depends on

- [Randomized-threshold and random-grid rounding lemmas](randomized-rounding-disagreement.md)
- [Two-sided Hoeffding inequality for averages of bounded variables](../../../../Probability/concentration-inequalities/hoeffding-s-inequality/measure-real-abs-avg-sub-ge-le.md)

## Sources

- R. Impagliazzo, R. Lei, T. Pitassi and J. Sorrell, "Reproducibility in Learning", Proceedings of the 54th Annual ACM SIGACT Symposium on Theory of Computing (STOC), 2022.
- W. Hoeffding, "Probability Inequalities for Sums of Bounded Random Variables", Journal of the American Statistical Association, 1963.
