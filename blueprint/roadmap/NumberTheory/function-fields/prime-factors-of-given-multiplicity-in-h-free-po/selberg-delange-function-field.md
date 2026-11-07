# Selberg–Delange theorem for function fields

Let $q > 1$ and $A > 0$ be real numbers,
and let $B_z(n)$ and $C_z(n)$ be complex numbers, for $z \in \mathbb{C}$ and integers $n \ge 0$,
such that for all $z$ and $n$

$$C_z(n) = \sum_{a=0}^{n} B_z(a)\, q^{n-a} \frac{(z)_{n-a}}{(n-a)!},$$

where $(z)_m = z(z+1)\cdots(z+m-1)$ is the rising factorial. Suppose there is a constant $M$
such that for every complex $z$ with $|z| \le A$ the series
$\sum_{n \ge 0} |B_z(n)| (n+1)^{2A+2} q^{-n}$ converges and its sum is at most $M$. Then there
is a constant $K$ such that for every complex $z$ with $|z| \le A$ and every integer $n \ge 1$,

$$\left| C_z(n) - \frac{q^n n^{z-1}}{\Gamma(z)} \sum_{a \ge 0} \frac{B_z(a)}{q^a} \right|
\le K q^n n^{\operatorname{Re} z - 2}.$$

In terms of the generating functions $B(u, z) = \sum_{n \ge 0} B_z(n) u^n$ and
$C(u, z) = \sum_{n \ge 0} C_z(n) u^n$, and with $Z_q(u) = (1 - qu)^{-1}$, the hypothesis on
$C_z(n)$ says $C(u, z) = B(u, z) Z_q(u)^z$, and the main term is
$q^n n^{z-1} B(1/q, z)/\Gamma(z)$. The paper's $q$ is the size of the field. The weight
$(n+1)^{2A+2}$ replaces the paper's $n^{2A+2}$: equivalent for $n \ge 1$, it also bounds
$B_z(0)$ uniformly, without which the conclusion fails (unbounded $B_z(0)$ along $z \to 2$
with $A = 2$).

## Sources

- Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9, Theorem 10 (`integers-2025-A9-thm-10`).
