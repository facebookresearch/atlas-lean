# Lorentzian polynomials as the closure of strictly Lorentzian polynomials

For all natural
numbers $n \ge 1$ and $d$, the closure of the set $\mathring{L}^d_n$ of strictly Lorentzian
polynomials of degree $d$ in $n$ variables, taken in the space $H^d_n$ of homogeneous polynomials
of degree $d$ in $\mathbb{R}[w_1, \dots, w_n]$ with the Euclidean topology on coefficients, is the
set $L^d_n$ of Lorentzian polynomials of degree $d$ in $n$ variables.

The hypothesis $n \ge 1$ excludes a degenerate case: for $n = 0$ and $d = 2$ the
$0 \times 0$ Hessian of a polynomial cannot have a positive eigenvalue, so $\mathring{L}^2_0$ is
empty, while $L^2_0 = S^2_0$ contains the zero polynomial, which is homogeneous of degree $2$.

The theorem says that the two definitions of Lorentzian polynomials agree: limits of strictly
Lorentzian polynomials (Definition 2.1) are exactly the polynomials of Definition 2.6, that is,
as the paper notes after the theorem, the homogeneous polynomials with nonnegative coefficients
and M-convex support whose quadratic derivatives $\partial^\alpha f$ have at most one positive
eigenvalue. The support condition cannot be dropped: for
$f = w_1^3 + w_2^3$ both partial derivatives are Lorentzian but $f$ is not (Example 2.4).
Brändén and Huh prove one inclusion with a Nuij-type homotopy (Theorem 2.13) and the other
through $c$-Rayleigh polynomials (Theorem 2.23 and Proposition 2.19).

## Sources

- P. Brändén and J. Huh, *Lorentzian polynomials*, Ann. of Math. 192 (2020), 821–891,
  Theorem 2.25, Example 2.4, https://arxiv.org/abs/1902.03719. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge. Problem `annals_lorentzian_polynomials` of the lean-eval benchmark.
