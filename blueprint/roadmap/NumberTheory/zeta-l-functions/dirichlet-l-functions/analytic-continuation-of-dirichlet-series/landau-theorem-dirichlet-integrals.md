# Landau's theorem on Dirichlet integrals with non-negative integrands

Let $A \colon [1, \infty) \to \mathbb{R}$ be locally bounded, that is, bounded on every interval
$[1, X]$, and Riemann integrable on every such interval, and suppose that for some $X_0 \ge 1$,
$A(x) \ge 0$ for every $x \ge X_0$. Let $\sigma_c$ be the infimum of the real numbers $\sigma$ for
which $\int_{X_0}^\infty A(x) x^{-\sigma} \, dx < \infty$, and suppose that $\sigma_c$ is finite. Then

$$F(s) = \int_1^\infty A(x) x^{-s} \, dx$$

is holomorphic on the half-plane $\operatorname{Re} s > \sigma_c$, and it does not extend to a
holomorphic function on any neighbourhood of $s = \sigma_c$.

It extends
[Landau's theorem that a Dirichlet series with non-negative coefficients](landau-theorem-dirichlet-series.md)
has a singularity at the real point of its abscissa of convergence, which concerns the summatory functions
$A(x) = \sum_{n \le x} a_n$ of non-negative sequences.

## Sources

- H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I. Classical Theory*, Cambridge
  Studies in Advanced Mathematics 97, Cambridge University Press, 2007, §15.1: Theorem 15.1 (this
  statement) and its applications in §15.1; Theorem 1.7 (Landau's theorem for Dirichlet series with
  non-negative coefficients), whose proof carries over.
- G. Martin, *MATH 539 notes, Tuesday, April 1, 2025*, University of British Columbia,
  <https://personal.math.ubc.ca/~gerg/teaching/539-Winter2025/Apr1.pdf>: the extension of Landau's
  theorem to Dirichlet integrals $F(s) = \int_1^\infty A(x) x^{-s} \, dx$ with $A$ non-negative,
  locally bounded and Riemann integrable (Montgomery–Vaughan, Theorem 15.1), and its use with
  $A(x) = x^{\Theta - \varepsilon} - (\psi(x) - x)$.
- K. S. Kedlaya, *Notes on analytic number theory*, online notes, Chapter 2, Section 2.1,
  <https://kskedlaya.org/ant/part-1-3.html>: Theorem 2.4 (Landau, for Dirichlet series with
  non-negative coefficients and their abscissa of absolute convergence) and its proof.
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  proves the form it needs, `Formalism.HC.Landau.landau_entire`, and applies it in
  `Formalism.HC.Landau.landau_family` to products of Dirichlet L-functions
  (`TotientGaloisClasses/Landau.lean`).
