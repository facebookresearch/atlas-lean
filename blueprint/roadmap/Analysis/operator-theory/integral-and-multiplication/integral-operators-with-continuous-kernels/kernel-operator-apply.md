# Evaluation formula for the integral operator

Let $\pi(t) = \max(0, \min(1, t))$ be the
projection of $\mathbb{R}$ onto $[0, 1]$. For a continuous kernel $k$ on $[0, 1] \times [0, 1]$,
write $T_k$ for the integral operator with kernel $k$ on $C([0, 1], \mathbb{R})$. For every
$f \in C([0, 1], \mathbb{R})$ and every $x \in [0, 1]$,

$$(T_k f)(x) = \int_0^1 k(x, \pi(t))\, f(\pi(t))\, dt,$$

the integral over $[0, 1]$ of the kernel integrand. Since $\pi(t) = t$ for $t \in [0, 1]$, this
is $\int_0^1 k(x, t)\, f(t)\, dt$.
