# Concatenated curve of two Loewner solutions

Let $W : \mathbb{R} \to \mathbb{R}$, $z \in \mathbb{C}$ and $S, T \in \mathbb{R}$. Let $\gamma$ be a [forward solution](loewner-forward-solution.md) of the Loewner equation driven by $W$ from $z$ on $[0, S]$, and let $\eta$ be a forward solution driven by $u \mapsto W(S + u)$ from $\gamma(S)$ on $[0, T]$. Their concatenated curve is

$$
t \mapsto \begin{cases} \gamma(t), & t \le S, \\ \eta(t - S), & t > S. \end{cases}
$$
