# Scalar product of symmetric polynomials

Let $n \ge 0$, let $R$ be a commutative ring, and
call a polynomial in $R[x_1, \dots, x_n]$ symmetric if it is unchanged by every permutation of the
variables. Let $a_\delta = \prod_{1 \le i < j \le n} (x_i - x_j)$, so that $a_\delta = 1$ when
$n \le 1$. For a sequence $\lambda = (\lambda_1, \dots, \lambda_n)$ of
integers with $\lambda_1 \ge \lambda_2 \ge \dots \ge \lambda_n \ge 0$, write $c_\lambda(P)$ for the
coefficient in a polynomial $P$ of the monomial
$x^{\lambda+\delta} = \prod_{i=1}^{n} x_i^{\lambda_i + n - i}$; when $n = 0$ the only such sequence
is the empty one and $x^{\lambda+\delta} = 1$. The scalar product of symmetric polynomials $f$ and
$g$ in $R[x_1, \dots, x_n]$ is

$$\langle f, g \rangle_n = \sum_{\lambda} c_\lambda(a_\delta f) \, c_\lambda(a_\delta g),$$

the sum taken over all sequences $\lambda$ as above; only finitely many terms are nonzero.
