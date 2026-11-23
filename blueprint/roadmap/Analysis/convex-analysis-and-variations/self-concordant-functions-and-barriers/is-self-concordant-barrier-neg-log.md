# $-\log$ is a $1$-self-concordant barrier for the nonnegative ray

The function $F(x) = -\log x$ is a [self-concordant barrier](is-self-concordant-barrier.md) with parameter $1$ for $[0, \infty)$, with interior $(0, \infty)$. Along a line, $DF(x)[h] = -h/x$, $D^2F(x)[h, h] = h^2/x^2$ and $D^3F(x)[h, h, h] = -2h^3/x^3$, so $|D^3F(x)[h,h,h]| = 2(D^2F(x)[h,h])^{3/2}$ and $|DF(x)[h]| = (D^2F(x)[h,h])^{1/2}$, with equality in both; $-\log x \to +\infty$ as $x \to 0^+$.

By the combination rules for sums and affine substitutions, $-\sum_i \log x_i$ is an $n$-self-concordant barrier for the nonnegative orthant and $-\sum_i \log(b_i - a_i^T x)$ an $m$-self-concordant barrier for a polyhedron with $m$ inequalities, the barriers of interior-point methods for linear programming.

## Sources

- A. Nemirovski, *Interior Point Polynomial Time Methods in Convex Programming*, lecture notes (Georgia Tech, 2004); author PDF at <https://www2.isye.gatech.edu/~nemirovs/Lect_IPM.pdf>, Example 2.1.2 (self-concordance of $-\ln t$ on the positive ray) and Example 3.1.2 (barrier parameter $1$).
