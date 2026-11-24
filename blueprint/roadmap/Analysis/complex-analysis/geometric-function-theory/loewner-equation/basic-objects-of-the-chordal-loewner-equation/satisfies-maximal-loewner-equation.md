# Maximal chordal Loewner evolution

Let $\mathbb{H}$ be the upper half-plane and $W : \mathbb{R} \to \mathbb{R}$. A family of sets $D_t \subseteq \mathbb{C}$ and maps $g_t : \mathbb{C} \to \mathbb{C}$, $t \in \mathbb{R}$, is a maximal chordal Loewner evolution driven by $W$ if:

- $D_0 = \mathbb{H}$, $g_0(z) = z$ for $z \in \mathbb{H}$, and $t \mapsto g_t(z)$ has right derivative $2/(z - W(0))$ at $t = 0$ for $z \in \mathbb{H}$;
- for every $t > 0$ and $z \in D_t$, $\partial_t g_t(z) = 2/(g_t(z) - W(t))$;
- $W$ is continuous;
- for every $t \ge 0$, $D_t$ is exactly the set of points whose Loewner trajectory [extends in $\mathbb{H}$ beyond $t$](has-loewner-forward-extension.md), and $g_t$ is a bijection from $D_t$ onto $\mathbb{H}$ that is conformal at every point of $D_t$.
