# Almost sure convergence of the empirical law in the Mallows metric

Let $E$ be a separable Banach space, $1 \le p < \infty$, and let $X_0, X_1, \dots$ be i.i.d. $E$-valued random variables whose law $\mu$ has a finite $p$-th moment $\int \|x\|^p \, d\mu(x) < \infty$. Let $F_n = \frac{1}{n+1} \sum_{i=0}^n \delta_{X_i}$ be the empirical law of the first $n + 1$ observations. Then, almost surely,

$$d_p(F_n, \mu) \to 0 .$$

For $p = 2$ on the line this is statement (2.1) of Bickel and Freedman, "$F_n \Rightarrow F$ in $\Gamma_2$ along almost all sample sequences", the first ingredient of the [bootstrap central limit theorem](bootstrap-mean-tendsto-gaussian-real.md). The empirical law is indexed by $n + 1$ observations to avoid the empty sample.

## Informally uses

- [The Wasserstein distance metrizes weak convergence in $P_p$](../../../MeasureTheory/optimal-transport/wasserstein-distances/tendsto-wasserstein-iff.md): Bickel and Freedman's Lemma 8.3, convergence in $d_p$ as weak convergence plus convergence of $p$-th moments.
- [Strong law of large numbers](../../laws-of-large-numbers/strong-law-of-large-numbers/README.md): for the $p$-th moments and for test functions.

## Sources

- P. J. Bickel and D. A. Freedman, "Some asymptotic theory for the bootstrap", *Ann. Statist.* 9 (1981) 1196–1217, Lemma 8.4 and statement (2.1).
