# From the minimal speed up, a heteroclinic orbit joins saddle and node

Let $D > 0$, $r > 0$ and $c \ge 2\sqrt{rD}$. Then there are $U, V : \mathbb{R} \to \mathbb{R}$ such
that $(U, V)$ is a
[traveling-wave profile](../../../Analysis/ordinary-differential-equations/is-wave-profile.md) of
speed $c$, so that $(U, V)$ solves the planar system $U' = V$, $V' = -(c V + r U(1 - U))/D$, with

- $(U(z), V(z)) \to (1, 0)$ as $z \to -\infty$ and $(U(z), V(z)) \to (0, 0)$ as $z \to +\infty$;
- $(U(z), V(z))$ in the open trapping triangle for every $z$, in particular $V(z) < 0$;
- $0 < U(z) < 1$ for every $z$, and $U$ strictly decreasing.

The open trapping triangle is $\{(u, v) : u < 1,\ v < 0,\ v + c u/(2D) > 0\}$, the interior of the
triangle with vertices $(0, 0)$, $(1, 0)$ and $(1, -c/(2D))$.
