# For weights summing to 1, $AX + b$ has covariance matrix $A C A^\top$

Let $\Omega$ be a finite set and $p : \Omega \to \mathbb{R}$ weights with
$\sum_{\omega \in \Omega} p(\omega) = 1$; they need not be nonnegative. For a map
$X : \Omega \to \mathbb{R}^n$ write $E_p[Y] = \sum_\omega p(\omega)\, Y(\omega)$ for the weighted
expectation of a real function $Y$ on $\Omega$, and $C_p(X)$ for the weighted covariance matrix
of $X$, with entries

$$C_p(X)_{jk} = \sum_{\omega \in \Omega} p(\omega)\,\bigl(X_j(\omega) - E_p[X_j]\bigr)\,
\bigl(X_k(\omega) - E_p[X_k]\bigr) .$$

Then for every real $m \times n$ matrix $A$ and every $b \in \mathbb{R}^m$,

$$C_p(AX + b) = A\, C_p(X)\, A^\top,$$

with the matrices multiplied in this order. The linear part, $C_p(AX) = A\, C_p(X)\, A^\top$,
holds for every real weight; the total weight $1$ makes the shift $b$ cancel in the centring. For
a probability distribution on $\Omega$ (also $p \ge 0$), $C_p(X)$ is the covariance matrix of the
random vector $X$, every moment being finite on a finite sample space, and the identity is exact
covariance propagation through an affine map.
