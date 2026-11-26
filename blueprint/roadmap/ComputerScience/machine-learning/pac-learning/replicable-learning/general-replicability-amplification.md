# Amplification of replicability from rho below one half

Let the output set have decidable equality and let $A$ be $\rho_0$-replicable over $\mathcal{D}$ with $\rho_0 < 1/2$. For every target $\rho > 0$ there is an algorithm built from $A$ that is $\rho$-replicable over $\mathcal{D}$: draw $T$ candidate shared seeds and one shared threshold, estimate for each candidate seed its collision probability and its strict-majority output from fresh blocks of samples, and output the majority output of the first seed whose estimated collision probability passes the threshold. For every $\beta > 0$ the parameters can be chosen so that, in addition, any such $A$ whose error is at most a threshold $\beta_0^{\mathrm{req}} > 0$ (depending on $\beta$ and the chosen parameters) yields an algorithm that errs with probability at most $\beta$. Quantitatively its disagreement is at most $(\mathrm{dis}_D(A)/(1 - \theta))^T$ plus twice the probability that some of the $T$ collision-probability estimates of one run is off by more than $\delta$, plus $T(2\delta/(b-a) + 1/N)$, for a window $\frac12 + \delta < a < b \le \theta - \delta$ with $\theta < 1$.

## Proof sketch

A seed whose two-run collision probability exceeds $\frac12$ has a strict-majority output that two independent runs find with high probability. By Markov's inequality on the disagreement over seeds, a random seed is bad with probability at most $\rho_0/(1-\theta)$, so with $T$ candidates some good seed appears except with probability $(\rho_0/(1-\theta))^T$. The shared random threshold makes both runs select the same first passing seed except with the rounding error, and accuracy follows from a union bound over candidate seeds.

## Depends on

- [Replicable algorithms with shared randomness](replicable-algorithms-with-shared-seed.md)
- [Randomized-threshold and random-grid rounding lemmas](randomized-rounding-disagreement.md)

## Proof depends on

- [Randomized-threshold and random-grid rounding lemmas](randomized-rounding-disagreement.md)

## Sources

- R. Impagliazzo, R. Lei, T. Pitassi and J. Sorrell, "Reproducibility in Learning", Proceedings of the 54th Annual ACM SIGACT Symposium on Theory of Computing (STOC), 2022.
