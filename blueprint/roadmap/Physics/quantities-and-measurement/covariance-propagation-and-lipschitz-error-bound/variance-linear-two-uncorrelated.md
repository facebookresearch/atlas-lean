# With zero covariance, weighted variances of $a_1X_1$ and $a_2X_2$ add

Let $\Omega$ be a finite set, $p : \Omega \to \mathbb{R}$ any real weights,
$X = (X_1, X_2) : \Omega \to \mathbb{R}^2$ and $a_1, a_2$ real numbers, and suppose that the
weighted covariance vanishes:

$$\mathrm{Cov}_p(X_1, X_2) = \sum_{\omega \in \Omega} p(\omega)\,\bigl(X_1(\omega) - E_p[X_1]\bigr)
\bigl(X_2(\omega) - E_p[X_2]\bigr) = 0,$$

where $E_p[Y] = \sum_\omega p(\omega)\, Y(\omega)$. Then, with the weighted variance
$\mathrm{Var}_p(Y) = \mathrm{Cov}_p(Y, Y)$,

$$\mathrm{Var}_p(a_1X_1 + a_2X_2) = a_1^2\, \mathrm{Var}_p(X_1) + a_2^2\, \mathrm{Var}_p(X_2) .$$

Since $\mathrm{Var}_p(a_k X_k) = a_k^2\, \mathrm{Var}_p(X_k)$ for every weight, the variances of
$a_1X_1$ and $a_2X_2$ add (addition in quadrature). Zero covariance is sufficient, not necessary:
in general the two sides differ by $2a_1a_2\, \mathrm{Cov}_p(X_1, X_2)$
([two-input formula](cov-matrix-two-linear.md)), which also vanishes when $a_1 = 0$ or $a_2 = 0$;
for correlated inputs with $a_1, a_2 \ne 0$ the cross term remains. For a probability
distribution on $\Omega$ ($p \ge 0$ and $\sum_\omega p(\omega) = 1$) the hypothesis says that
$X_1$ and $X_2$ are uncorrelated.
