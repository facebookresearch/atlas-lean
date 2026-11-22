# Spectral decomposition of the Dirichlet Green's operator

Write $L^2([0, 1])$ for the real
Hilbert space of square-integrable functions on $[0, 1]$ with Lebesgue measure, let
$G(x, t) = \min(x, t)\,(1 - \max(x, t))$ be the Green's kernel, and for each positive integer $k$
let $u_k(x) = \sqrt{2} \sin(k\pi x)$ and $\lambda_k = \frac{1}{k^2\pi^2}$. Let $A$ be a linear map
from $L^2([0, 1])$ to itself that is symmetric, $\langle Af, g \rangle = \langle f, Ag \rangle$ for
all $f, g$, and is given by the Green's kernel, $(Af)(x) = \int_{[0, 1]} G(x, t) f(t)\, dt$ for
almost every $x \in [0, 1]$ and every $f$. Let $(b_k)_{k \ge 1}$ be a Hilbert basis of
$L^2([0, 1])$ indexed by the positive integers with $b_k = u_k$ almost everywhere on $[0, 1]$.
Then $A$ is injective, each $b_k$ is an eigenvector of $A$ with eigenvalue $\lambda_k$, and every
$f \in L^2([0, 1])$ satisfies $Af = \sum_{k \ge 1} \lambda_k \langle b_k, f \rangle\, b_k$.
