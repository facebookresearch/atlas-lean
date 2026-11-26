# Absolute residual score of a fitting algorithm

Let $A$ be a fitting algorithm that maps a data vector $z$ of length $n + 1$ to a regression
function $\hat\mu = A(z) : \mathcal X \to \mathbb{R}$. Its absolute residual score is
$S(z)_i = \lvert y_i - \hat\mu(x_i) \rvert$, the residual of point $i$ under the fit trained on all
$n + 1$ points. Evaluated on the augmented data $(z_1, \dots, z_n, (x, y))$, these are the residuals
$R_{y,i}$ of Lei et al., equation (4), with $\hat\mu_y = A(z_1, \dots, z_n, (x, y))$.

## Sources

- J. Lei, M. G'Sell, A. Rinaldo, R. J. Tibshirani and L. Wasserman, *Distribution-free predictive inference for regression*, arXiv:1604.04173v2 (9 March 2017); published in J. Amer. Statist. Assoc. 113 (2018) 1094–1111. Theorem and equation numbers refer to the arXiv version, which is the one read. Equation (4).
