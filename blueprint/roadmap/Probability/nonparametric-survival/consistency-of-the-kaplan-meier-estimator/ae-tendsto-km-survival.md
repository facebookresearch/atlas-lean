# Consistency of the Kaplan–Meier estimator at a grid time

Let the subjects $Z_i = (T_i, C_i)$ be independent, each with the law of the independent censoring
model: the product of a law of $T$ and a law of $C$ on the grid $\{0, 1, \dots, k - 1\}$. If the
observed at-risk mass $\Pr[\min(T, C) \ge m]$ is nonzero, then almost surely the Kaplan–Meier estimate
$\hat S_n(m)$ of the first $n$ subjects at the grid time $m$ converges to $\prod_{j \le m} (1 - h(j))$,
where $h$ is the discrete hazard of $T$. By the discrete product-limit identity this limit is
$\Pr[T > m]$. This is consistency for the survival function of $T$ at grid points only.
