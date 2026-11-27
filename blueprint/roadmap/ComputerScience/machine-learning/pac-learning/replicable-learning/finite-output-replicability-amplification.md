# Replicability from accuracy for finite output sets

Let the output set $\mathcal{Y}$ be finite with $M = |\mathcal{Y}|$ elements, linearly ordered, and let $A$ (with no replicability assumption) err with probability at most $\beta_0 < 1/(M+1)$ over $\mathcal{D}$, where erring means producing an output outside $\mathrm{good}(D)$. For all $\rho, \beta > 0$ there are thresholds $a < b$ and integers $k, N \ge 1$ such that the following algorithm is strongly $\rho$-replicable and errs with probability at most $\beta$ over $\mathcal{D}$: run $A$ with fresh internal randomness on $k$ disjoint blocks, draw one shared threshold $\theta$ from the grid of $N$ points in $[a, b)$, and output the least element whose empirical frequency among the $k$ runs is at least $\theta$. Quantitatively, for $\delta \ge 0$ it is strongly $\rho$-replicable with $\rho = 4Me^{-2k\delta^2} + M(2\delta/(b-a) + 1/N)$, and if $\beta_0 + \delta < a \le b \le (1-\beta_0)/M - \delta$ it errs with probability at most $2Me^{-2k\delta^2}$.

## Proof sketch

By Hoeffding's inequality, all $M$ empirical frequencies are within $\delta$ of the true output probabilities except with probability $2Me^{-2k\delta^2}$ per run. Some good output has probability at least $(1-\beta_0)/M$ while every bad one has probability at most $\beta_0$, so the window $[a,b)$ separates them. Two runs output differently only if a shared threshold falls between corresponding frequencies, which the threshold-rounding lemma bounds per element.

## Depends on

- [Replicable algorithms with shared randomness](replicable-algorithms-with-shared-seed.md)
- [Randomized-threshold and random-grid rounding lemmas](randomized-rounding-disagreement.md)
- [Two-sided Hoeffding inequality for averages of bounded variables](../../../../Probability/concentration-inequalities/hoeffding-s-inequality/measure-real-abs-avg-sub-ge-le.md)

## Proof depends on

- [Randomized-threshold and random-grid rounding lemmas](randomized-rounding-disagreement.md)
- [Two-sided Hoeffding inequality for averages of bounded variables](../../../../Probability/concentration-inequalities/hoeffding-s-inequality/measure-real-abs-avg-sub-ge-le.md)

## Sources

- R. Impagliazzo, R. Lei, T. Pitassi and J. Sorrell, "Reproducibility in Learning", Proceedings of the 54th Annual ACM SIGACT Symposium on Theory of Computing (STOC), 2022.
