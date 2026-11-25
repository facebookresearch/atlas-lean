# The set of Lorentzian polynomials

For natural numbers $n$ and $d$, the set $L^d_n$ of
Lorentzian polynomials is a set of homogeneous polynomials of degree $d$ in
$\mathbb{R}[w_1, \dots, w_n]$, defined by recursion on $d$. For $d \le 2$, $L^d_n = S^d_n$, the set
of homogeneous stable polynomials of degree $d$ with nonnegative coefficients. For $d \ge 3$,
$L^d_n$ is the set of $f \in M^d_n$ (the homogeneous polynomials of degree $d$ with nonnegative
coefficients and M-convex support) such that $\partial_i f \in L^{d-1}_n$ for every
$i \in \{1, \dots, n\}$, where $\partial_i$ is the partial derivative with respect to $w_i$.

This is Definition 2.6 of Brändén and Huh. By
[their Theorem 2.25](theorem-2-25.md) it is, for $n \ge 1$, the closure of the set of strictly Lorentzian polynomials, and in two variables it consists of the forms whose coefficients are nonnegative,
ultra log-concave and without internal zeros ([bivariate Lorentzian polynomials](bivariate-mem-l-iff.md)).

## Sources

- P. Brändén and J. Huh, *Lorentzian polynomials*, Ann. of Math. 192 (2020), 821–891,
  Definition 2.6, https://arxiv.org/abs/1902.03719.
