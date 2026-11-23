# Kernel integrand

Let $\pi(t) = \max(0, \min(1, t))$ clamp a real number $t$ to $[0, 1]$.
For a continuous kernel $k$ on $[0, 1] \times [0, 1]$, a bounded continuous function $f$ on
$[0, 1]$ and a point $x \in [0, 1]$, the kernel integrand is the function
$\mathbb{R} \to \mathbb{R}$, $t \mapsto k(x, \pi(t)) \, f(\pi(t))$.
