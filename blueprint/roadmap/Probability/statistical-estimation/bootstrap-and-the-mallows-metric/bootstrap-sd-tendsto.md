# Consistency of the bootstrap standard deviation

Under the hypotheses of the [bootstrap central limit theorem](bootstrap-mean-tendsto-gaussian-real.md), let $s^*_m = \bigl(\frac1m \sum_{j=1}^m (X^*_j - \mu^*_m)^2\bigr)^{1/2}$ be the standard deviation of the bootstrap sample. Along almost every sample sequence, $s^*_m \to \sigma$ in conditional probability as $n, m \to \infty$: for every $\varepsilon > 0$,

$$P\{|s^*_m - \sigma| > \varepsilon \mid X_0, \dots, X_n\} \to 0 .$$

Together with part (a), the bootstrap law of the pivot $\sqrt m (\mu^*_m - \mu_n) / s^*_m$ has the same normal limit as the classical pivot.

The conditional probability is the proportion of resampling maps $I : \{1, \dots, m\} \to \{0, \dots, n\}$ for which $|s^*_m - \sigma| > \varepsilon$.

## Sources

- P. J. Bickel and D. A. Freedman, "Some asymptotic theory for the bootstrap", *Ann. Statist.* 9 (1981) 1196–1217, Theorem 2.1(b).
