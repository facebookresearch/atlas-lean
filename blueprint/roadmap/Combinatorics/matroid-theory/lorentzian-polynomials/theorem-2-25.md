# Lorentzian polynomials as the closure of strictly Lorentzian polynomials

For all natural
numbers $n \ge 1$ and $d$, the closure of the set $\mathring{L}^d_n$ of strictly Lorentzian
polynomials of degree $d$ in $n$ variables, taken in the space $H^d_n$ of homogeneous polynomials
of degree $d$ in $\mathbb{R}[w_1, \dots, w_n]$ with the Euclidean topology on coefficients, is the
set $L^d_n$ of Lorentzian polynomials of degree $d$ in $n$ variables.

The paper (Theorem 2.25) allows $n = 0$, but the statement fails for $n = 0$ and $d = 2$: the
$0 \times 0$ Hessian of a polynomial cannot have a positive eigenvalue, so $\mathring{L}^2_0$ is
empty, while $L^2_0 = S^2_0$ contains the zero polynomial, which is homogeneous of degree $2$.

## Sources

- P. Brändén and J. Huh, `Lorentzian polynomials`, Annals of Math, 192 (3) 2020. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2020-192-3-LorentzianPolynomials.lean Via leanprover/lean-eval@38361be, problem `annals_lorentzian_polynomials`.
