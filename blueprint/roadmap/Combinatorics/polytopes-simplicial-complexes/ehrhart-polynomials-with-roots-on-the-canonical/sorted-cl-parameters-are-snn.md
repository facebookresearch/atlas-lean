# Small sorted CL parameters give an SNN polynomial

Let $f$ be a complex polynomial of
degree $d$, let $a > 0$ be real, and let $c_0 \le c_1 \le \dots \le c_{m-1}$ be real numbers, each
at least $1/4$, with $m = \lfloor d/2 \rfloor$, such that $f = a \prod_{k=0}^{m-1} (X^2 + X + c_k)$
if $d$ is even and $f = a (2X + 1) \prod_{k=0}^{m-1} (X^2 + X + c_k)$ if $d$ is odd. Suppose that
$c_k \le 2k + 2$ for every $k$ when $d$ is odd, and $c_k \le 2k + 1$ for every $k$ when $d$ is
even. Then $f$ is an SNN polynomial.

The hypothesis $a > 0$ is needed: for $d = 1$, $a = -1$ and no parameters, $f = -(2X + 1)$ is not
SNN, since its zeroth $h^*$-coefficient is $f(0) = -1 < 0$.

## Sources

- Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*, INTEGERS 25 (2025), Article A68, Proposition 5.
