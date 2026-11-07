# Selberg–Delange theorem, $h$-th power version

Let $q > 1$ and $A > 0$ be real numbers,
let $h \ge 1$ be an integer, let $\xi$ be a primitive $h$-th root of unity in $\mathbb{C}$, and
let $B_z(n)$ and $C_z(n)$ be complex numbers, for $z \in \mathbb{C}$ and integers $n \ge 0$,
such that for all $z$ and $n$

$$C_z(n) = \sum_{\substack{0 \le a \le n \\ h \mid n - a}} B_z(a)\, q^{(n-a)/h}
\frac{(z)_{(n-a)/h}}{((n-a)/h)!},$$

where $(z)_m = z(z+1)\cdots(z+m-1)$ is the rising factorial. Suppose there is a constant $M$
such that for every complex $z$ with $|z| \le A$ the series
$\sum_{n \ge 0} |B_z(n)| (n+1)^{2A+2} q^{-n/h}$ converges and its sum is at most $M$. Then there
is a constant $K$ such that for every complex $z$ with $|z| \le A$ and every integer $n \ge 1$,

$$\left| C_z(n) - \frac{q^{n/h} n^{z-1}}{h^z \Gamma(z)} \sum_{j=0}^{h-1} \xi^{jn}
\sum_{a \ge 0} B_z(a) \left(q^{1/h} \xi^j\right)^{-a} \right|
\le K q^{n/h} n^{\operatorname{Re} z - 2}.$$

In terms of the generating functions $B(u, z) = \sum_{n \ge 0} B_z(n) u^n$ and
$C(u, z) = \sum_{n \ge 0} C_z(n) u^n$, and with $Z_q(u) = (1 - qu)^{-1}$, the hypothesis on
$C_z(n)$ says $C(u, z) = B(u, z) Z_q(u^h)^z$, and the inner sums are
$B((q^{1/h} \xi^j)^{-1}, z)$. The paper's $q$ is the size of the field. As in the case $h = 1$,
the weight is $(n+1)^{2A+2}$ rather than $n^{2A+2}$, so that $B_z(0)$ is bounded uniformly.

## Sources

- Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9, Theorem 11 (`integers-2025-A9-thm-11`).
