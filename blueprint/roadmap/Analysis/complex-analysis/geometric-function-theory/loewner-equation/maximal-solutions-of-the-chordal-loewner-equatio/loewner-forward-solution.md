# Forward solution of the Loewner equation

Let $\mathbb{H} = \{w \in \mathbb{C} : \operatorname{Im} w > 0\}$, let $W : \mathbb{R} \to \mathbb{R}$ be a driving function, $z \in \mathbb{C}$ and $T \in \mathbb{R}$. A forward solution of the chordal Loewner equation from $z$ on $[0, T]$ is a curve $\gamma : \mathbb{R} \to \mathbb{C}$, $t \mapsto g_t(z)$, with $\gamma(0) = z$ such that, for every $t \in [0, T]$, $\gamma(t) \in \mathbb{H}$ and $\gamma$ has derivative

$$
\gamma'(t) = \frac{2}{\gamma(t) - W(t)}
$$

at $t$ within $[0, T]$. For $T > 0$ the derivatives at the endpoints are one-sided. For $T = 0$ the derivative condition within $\{0\}$ is vacuous, so the only requirement is $\gamma(0) = z \in \mathbb{H}$; for $T < 0$ the interval is empty and only $\gamma(0) = z$ is required.
