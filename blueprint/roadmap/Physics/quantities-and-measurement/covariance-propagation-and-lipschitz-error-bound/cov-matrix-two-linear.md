# Weighted variance of $a_1X_1 + a_2X_2$ with the covariance cross term

Let $\Omega$ be a finite set, $p : \Omega \to \mathbb{R}$ any real weights,
$X = (X_1, X_2) : \Omega \to \mathbb{R}^2$ and $a_1, a_2$ real numbers. With the weighted
expectation $E_p[Y] = \sum_\omega p(\omega)\, Y(\omega)$, the weighted covariance
$\mathrm{Cov}_p(Y, Z) = E_p\bigl[(Y - E_p[Y])(Z - E_p[Z])\bigr]$ and the weighted variance
$\mathrm{Var}_p(Y) = \mathrm{Cov}_p(Y, Y)$,

$$\mathrm{Var}_p(a_1X_1 + a_2X_2) = a_1^2\, \mathrm{Var}_p(X_1) + a_2^2\, \mathrm{Var}_p(X_2) +
2a_1a_2\, \mathrm{Cov}_p(X_1, X_2) .$$

The left side is the single entry of the weighted covariance matrix of the one-coordinate vector
$(a_1 \;\, a_2)\, X$. The identity is the propagation rule $C_p(AX) = A\, C_p(X)\, A^\top$, valid
for every weight, for the $1 \times 2$ matrix $A = (a_1 \;\, a_2)$, together with the symmetry
$\mathrm{Cov}_p(X_2, X_1) = \mathrm{Cov}_p(X_1, X_2)$; no independence is assumed. For a
probability distribution on $\Omega$ ($p \ge 0$ and $\sum_\omega p(\omega) = 1$) these are the
variance and covariance of the random variables $X_1$ and $X_2$; for other weights they are only
these weighted sums. With zero covariance the cross term drops
([addition in quadrature](variance-linear-two-uncorrelated.md)).
