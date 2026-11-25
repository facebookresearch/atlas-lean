# Permutation-equivariant score map

A map $S$ from data vectors $z = (z_1, \dots, z_{n+1})$ to score vectors in $\mathbb{R}^{n+1}$ is
permutation equivariant if permuting the data points permutes the scores in the same way:
$S(z \circ \sigma) = S(z) \circ \sigma$ for every permutation $\sigma$ of $\{1, \dots, n+1\}$.

Scores of the form $S(z)_i = f(z_{-i}; z_i)$, with $f$ symmetric in its first $n$ arguments, have
this property; these are the conformity scores of Lei et al., Remark 2.4. So do the absolute
residuals of a fitting algorithm that is symmetric in the data.

## Sources

- J. Lei, M. G'Sell, A. Rinaldo, R. J. Tibshirani and L. Wasserman, *Distribution-free predictive inference for regression*, arXiv:1604.04173v2 (9 March 2017); published in J. Amer. Statist. Assoc. 113 (2018) 1094–1111. Theorem and equation numbers refer to the arXiv version, which is the one read. Remark 2.4.
