# Concatenation of Loewner forward solutions

Let $W : \mathbb{R} \to \mathbb{R}$, $z \in \mathbb{C}$ and $S, T \ge 0$. Let $\gamma$ be a [forward solution](loewner-forward-solution.md) of the Loewner equation driven by $W$ from $z$ on $[0, S]$, and let $\eta$ be a forward solution driven by $u \mapsto W(S + u)$ from $\gamma(S)$ on $[0, T]$. Then their [concatenated curve](append-curve.md), equal to $\gamma(t)$ for $t \le S$ and to $\eta(t - S)$ for $t > S$, is a forward solution driven by $W$ from $z$ on $[0, S + T]$.
