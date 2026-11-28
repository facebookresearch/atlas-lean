# Cox estimator of the first n observations

For a sequence of observations $(T_i, d_i, z_i)$ (observed time, event flag, scalar covariate), the Cox estimator of the first $n$ is the maximum partial likelihood estimator of the data $(T_i, \mathbf 1\{d_i = 1\}, z_i)$, $i < n$: the value $d_i = 1$ marks an observed event and any other value a censoring, and the estimator is a maximizer of the scalar log partial likelihood when one exists and $0$ otherwise.
