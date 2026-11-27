# Shifts at the same starting counter add up

Let $Y$ be an additive commutative group. For every function $f \colon \mathbb{Z}/N \to Y$, every starting counter $r_s$ and all $u, v \in Y^\ell$, shifting twice at the **same** start $r_s$ is one shift by the sum:

$$
\mathrm{ctrShift}(\mathrm{ctrShift}(f, r_s, u), r_s, v) = \mathrm{ctrShift}(f, r_s, u + v),
$$

where [$\mathrm{ctrShift}(f, r_s, v)$](ctr-shift.md) adds $\sum_{i < \ell,\ r_s + i = x} v_i$ to $f(x)$. Shifts with different starts can change different coordinates.
