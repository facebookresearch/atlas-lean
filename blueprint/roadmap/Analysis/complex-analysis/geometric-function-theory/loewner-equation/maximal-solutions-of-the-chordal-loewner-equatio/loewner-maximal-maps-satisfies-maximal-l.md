# Maximal Loewner maps solve the maximal Loewner equation

Let $\mathbb{H}$ be the upper half-plane and let $W : \mathbb{R} \to \mathbb{R}$ be continuous. The [unswallowed domains](loewner-unswallowed-domain.md) $H_t$ and the [Loewner maps](loewner-maximal-maps.md) $g_t$ solve the maximal chordal Loewner equation:

- $H_0 = \mathbb{H}$, $g_0(z) = z$ for $z \in \mathbb{H}$, and $t \mapsto g_t(z)$ has right derivative $2/(z - W(0))$ at $t = 0$;
- for every $t > 0$ and $z \in H_t$, $\partial_t g_t(z) = 2/(g_t(z) - W(t))$;
- for every $t \ge 0$, $H_t$ is the set of points whose Loewner trajectories extend in $\mathbb{H}$ beyond $t$, and $g_t$ is a bijection from $H_t$ onto $\mathbb{H}$ that is conformal at every point of $H_t$.
