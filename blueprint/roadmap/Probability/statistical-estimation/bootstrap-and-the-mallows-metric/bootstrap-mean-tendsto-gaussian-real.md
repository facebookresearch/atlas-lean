# Bickel–Freedman bootstrap central limit theorem for the mean

Let $X_0, X_1, \dots$ be i.i.d. real random variables with finite positive variance $\sigma^2$, and let $\mu_n$ be the mean of $X_0, \dots, X_n$. Given the data, let $X^*_1, \dots, X^*_m$ be drawn independently and uniformly from $X_0, \dots, X_n$, with mean $\mu^*_m$. Along almost every sample sequence, as $n$ and $m$ tend to infinity jointly, the conditional law of

$$\sqrt m \, (\mu^*_m - \mu_n)$$

given the data converges weakly to $N(0, \sigma^2)$.

A bootstrap sample is written as $X_{I(1)}, \dots, X_{I(m)}$ for a uniformly random map $I : \{1, \dots, m\} \to \{0, \dots, n\}$, so the conditional expectation of $f(\sqrt m (\mu^*_m - \mu_n))$ is the average of that quantity over the $(n+1)^m$ maps $I$. Weak convergence is tested against every bounded continuous $f$, and "$n, m \to \infty$ jointly" means convergence along the product of the filters $n \to \infty$ and $m \to \infty$. The sample has $n + 1$ points to avoid the empty sample.

Bickel and Freedman's proof: the conditional law of $\sqrt m (\mu^*_m - \mu_n)$ is $F_n^{(m)}$ in the notation of [Mallows' contraction](wasserstein-two-normalized-sum-le.md). Almost surely $F_n \to F$ in $d_2$, so $d_2(F_n^{(m)}, F^{(m)}) \le d_2(F_n, F) \to 0$ uniformly in $m$, while $F^{(m)} \to N(0, \sigma^2)$ by the central limit theorem; and convergence in $d_2$ implies weak convergence.

## Informally uses

- [Almost sure convergence of the empirical law in the Mallows metric](tendsto-wasserstein-empirical.md): statement (2.1), $F_n \to F$ in $d_2$.
- [Mallows' contraction of normalised sums](wasserstein-two-normalized-sum-le.md): statement (2.2), $d_2(F_n^{(m)}, F^{(m)}) \le d_2(F_n, F)$.
- [Lindeberg–Feller central limit theorem](../../central-limit-theorems/lindeberg-feller-central-limit-theorem/README.md): the ordinary central limit theorem for $F^{(m)}$, its i.i.d. special case.
- [Convergence in $W_p$ implies weak convergence](../../../MeasureTheory/optimal-transport/wasserstein-distances/wasserstein-convergence/tendsto-of-tendsto-wasserstein.md): to pass from $d_2$ to weak convergence.

## Sources

- P. J. Bickel and D. A. Freedman, "Some asymptotic theory for the bootstrap", *Ann. Statist.* 9 (1981) 1196–1217, Theorem 2.1(a) and its proof.
