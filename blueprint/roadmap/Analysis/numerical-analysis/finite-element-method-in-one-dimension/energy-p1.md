# Energy pairing with a P1 function via nodal differences

Let $0 = x_0 < \dots < x_n = 1$ be a partition of $[0, 1]$ and let $w : \mathbb{R} \to \mathbb{R}$ be
continuous on each element $[x_i, x_{i+1}]$, differentiable at every point of each open element
$(x_i, x_{i+1})$, with $w'$ integrable on each element. Then for every nodal vector
$d \in \mathbb{R}^{n+1}$, with $p_d$ the [P1 function](p1.md) and $s_i(d)$ the [element
slopes](element-slope.md),

$$a(w, p_d) = \sum_{i=0}^{n-1} s_i(d)\, \big(w(x_{i+1}) - w(x_i)\big),$$

where $a(u, v) = \int_0^1 u' v'$ is the [energy form](energy.md). This is the key identity of the
one-dimensional P1 method.
