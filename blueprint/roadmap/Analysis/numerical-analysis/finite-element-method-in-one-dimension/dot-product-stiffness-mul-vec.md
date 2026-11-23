# Quadratic form of the stiffness matrix

Let $0 = x_0 < \dots < x_n = 1$ be a partition of $[0, 1]$ with element lengths $h_i = x_{i+1} - x_i$
and [stiffness matrix](stiffness.md) $K$. For all $c, d \in \mathbb{R}^{n+1}$,

$$d^{\mathsf T} K c = \sum_{i=0}^{n-1} \frac{(c_{i+1} - c_i)(d_{i+1} - d_i)}{h_i} .$$
