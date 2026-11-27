# Continuity and linearity of the driving functional

Let $T \ge 0$, $t \in [0, T]$, $c_0, \ell \in \mathbb{R}^2$ and
$\kappa : \mathbb{R} \to \mathbb{R}^2$ continuous on $[0, t]$. Then there is a continuous linear
functional $\Lambda$ on $\mathbb{R}^2 \times C([0, T], \mathbb{R}^2)$ with

$$
\Lambda(u, f) = \langle c_0, u \rangle + \langle \ell, f(t) - f(0) \rangle +
\int_0^t \langle \kappa(s), f(s) - f(0) \rangle\, ds
$$

for every initial value $u$ and every continuous path $f$ on $[0, T]$, with the
[dot product](dot.md).
