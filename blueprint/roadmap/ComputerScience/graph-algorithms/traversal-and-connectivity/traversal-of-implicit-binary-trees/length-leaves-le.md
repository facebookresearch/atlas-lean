# Binomial bound on the frontier size under depth and heavy budgets

Let a branching step send a branching state to its pair (light child, heavy child). Let
$D, T, q \in \mathbb{N}$ and let $G(s, p, t)$ be a relation between states and natural numbers
(read: $s$ is reached having used depth $p$ and heavy budget $t$) such that

- $G(s, p, t)$ implies $p \le D$ and $t \le T$;
- if $G(s, p, t)$ and $s$ branches into $(l, h)$, then $G(l, p + 1, t)$ and $G(h, p + 1, t + q)$.

Let $k, d, m \in \mathbb{N}$ and $s$ a state with $G(s, p, t)$ for some $p, t$ such that
$D \le p + d$ and $T < t + (m + 1) q$. Then the frontier of $s$ cut at depth $k$ has length at
most

$$\sum_{j=0}^{m} \binom{d}{j}.$$
