# Landau's theorem on Dirichlet series with non-negative coefficients

Let $f(s) = \sum_{n \ge 1} a_n n^{-s}$ be a Dirichlet series with real coefficients $a_n \ge 0$,
and suppose that its abscissa of absolute convergence $\sigma_a$ is a real number. Then $f$, which
is holomorphic on the half-plane $\operatorname{Re} s > \sigma_a$, does not extend to a holomorphic
function on any neighbourhood of $s = \sigma_a$.

The proof expands $f$ in a power series about a real point $c > \sigma_a$: all its coefficients
$\sum_n a_n n^{-c} (\log n)^k / k!$ are non-negative, so if $f$ were holomorphic near $\sigma_a$ the
double series would converge absolutely at a real point to the left of $\sigma_a$, and so would the
Dirichlet series.

## Sources

- K. S. Kedlaya, *Notes on analytic number theory*, online notes, Chapter 2, Section 2.1,
  <https://kskedlaya.org/ant/part-1-3.html>: Lemma 2.2 and Definition 2.3 (the abscissa of absolute
  convergence), Theorem 2.4 (Landau: "Let $f(s) = \sum_{n=1}^\infty a_n n^{-s}$ be a Dirichlet series
  with nonnegative real coefficients. Suppose $L \in \mathbb{R}$ is the abscissa of absolute
  convergence for $f(s)$. Then $f$ cannot be extended to a holomorphic function on any neighborhood
  of $s = L$.") and its proof.
- H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I. Classical Theory*, Cambridge
  Studies in Advanced Mathematics 97, Cambridge University Press, 2007, Theorem 1.7.
