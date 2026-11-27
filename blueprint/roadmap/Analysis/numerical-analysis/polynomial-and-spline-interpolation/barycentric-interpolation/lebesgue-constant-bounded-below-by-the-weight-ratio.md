# The Lebesgue constant is bounded below by the ratio of the barycentric weights

Let $n \ge 1$, let $a < b$, and let $x_0, \dots, x_n$ be distinct nodes in $[a, b]$ with [barycentric weights](barycentric-weights.md) $w_j$, and let $\Lambda_n = \max_{x \in [a, b]} \sum_{j=0}^n |\ell_j(x)|$ be the Lebesgue constant, the norm on $C[a, b]$ of the map that sends $f$ to its interpolating polynomial, where $\ell_j$ are the Lagrange basis polynomials. Then

$$\Lambda_n \ge \frac{1}{2n^2}\, \frac{\max_j |w_j|}{\min_j |w_j|} .$$

Widely varying weights therefore force ill-conditioned interpolation.

## Depends on

- [Barycentric weights](barycentric-weights.md)
- [Lebesgue function](../../../approximation-theory/lagrange-interpolation/lebesgue-function.md)
- [Lagrange interpolation](../../../approximation-theory/lagrange-interpolation/eval-interpolant.md)
- [Evaluated Lagrange basis polynomial](../../../approximation-theory/lagrange-interpolation/eval-basis.md)

## Expansion

This page becomes ready once:

- Proof prerequisite: Markov's inequality for polynomial derivatives, as a page of its own: a real polynomial $p$ of degree at most $n$ satisfies $\max_{[a,b]} |p'| \le \frac{2n^2}{b - a} \max_{[a,b]} |p|$. The proof applies it to the Lagrange basis polynomials, using $|w_i / w_j| = |x_j - x_i|\,|\ell_i'(x_j)|$ for $i \ne j$.

## Sources

- J.-P. Berrut and L. N. Trefethen, "Barycentric Lagrange interpolation", *SIAM Review* 46(3):501–517, 2004, Section 9.1, the Lebesgue constant (9.1), its expression through the Lagrange polynomials, and the lower bound (9.2), derived there from Markov's inequality for derivatives of polynomials. <https://people.maths.ox.ac.uk/trefethen/barycentric.pdf>
