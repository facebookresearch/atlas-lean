# Quadrature rule

Let $a < b$. A *weight function* on $[a, b]$ is a continuous function $w : (a, b) \to [0, \infty)$ that is integrable on $(a, b)$ with $0 < \int_a^b w(x)\, dx < \infty$; it may be unbounded near the endpoints, as $w(x) = 1/\sqrt{1 - x^2}$ on $(-1, 1)$, with integral $\pi$, for Gauss–Chebyshev quadrature. Since $[a, b]$ is bounded, $\int_a^b |x|^k w(x)\, dx$ is finite for every $k$. A *quadrature rule* with $n + 1$ nodes for the weight $w$ is an approximation

$$\int_a^b f(x)\, w(x)\, dx \approx \sum_{i=0}^{n} A_i f(x_i)$$

with nodes $x_0, \dots, x_n \in [a, b]$ and real coefficients (weights) $A_0, \dots, A_n$, for $f$ bounded and defined at every point of $[a, b]$ with $f w$ integrable on $(a, b)$, for example $f$ continuous on $[a, b]$ or a step function. The rule is *exact* on the polynomials of degree at most $m$ if equality holds for every such polynomial $f$; since both sides are linear in $f$, it suffices that it holds for $f(x) = x^k$, $0 \le k \le m$. The case $w \equiv 1$ is the unweighted integral $\int_a^b f(x)\, dx$.

## Sources

- D. Levy, *Introduction to Numerical Analysis*, lecture notes, Department of Mathematics, University of Maryland, version of 4 January 2021, Section 6.2 (quadratures (6.7)–(6.9)), Section 6.4.1 (exactness on $1, x, x^2$ and linearity), and Section 6.6 (weight functions and the weighted quadrature (6.27)). <https://www.math.umd.edu/~dlevy/resources/notes.pdf>
