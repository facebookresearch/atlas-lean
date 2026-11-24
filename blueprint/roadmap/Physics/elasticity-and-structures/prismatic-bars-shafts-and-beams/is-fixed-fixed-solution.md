# Fixed-fixed problem for a bar or shaft of constant rigidity

Let $k$ and $L$ be real numbers and $f, u \colon \mathbb{R} \to \mathbb{R}$. The function $u$ solves
the fixed-fixed problem on $[0, L]$ with rigidity $k$ and distributed load $f$ if $u$ is twice
continuously differentiable on $[0, L]$,

$$-k\, u''(x) = f(x) \qquad \text{for every } x \in [0, L],$$

with the second derivative taken within $[0, L]$ (one-sided at the ends), and $u(0) = u(L) = 0$.

For a bar, $k = EA$ is the axial rigidity, $f$ the distributed axial load (force per length,
positive in the direction of increasing $x$) and $u$ the axial displacement: the equation is the
equilibrium $(k u')' + f = 0$ of the internal axial force $k u'$ of a small-strain linear elastic
bar fixed at both ends. For a circular shaft in Saint-Venant torsion, $k = GJ$ is the torsional
rigidity, $f$ the distributed torque and $u$ the twist angle. The model has $L > 0$ and $k > 0$; the
definition allows any real $k$ and $L$. For $L < 0$ the interval is empty and only $u(0) = u(L) = 0$
remains; for $L = 0$ the second derivative within $\{0\}$ is $0$ by convention, so the conditions
reduce to $u(0) = 0$ and $f(0) = 0$.
