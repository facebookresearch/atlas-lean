# A large enough depth cut yields only terminal states

Let $D, T, q \in \mathbb{N}$ and let $G(s, p, t)$ be a relation between states and natural numbers
such that $G(s, p, t)$ implies $p \le D$ and $t \le T$, and such that if $G(s, p, t)$ and $s$
branches into $(l, h)$ then $G(l, p + 1, t)$ and $G(h, p + 1, t + q)$. Let $k \in \mathbb{N}$ and
$s$ a state with $G(s, p, t)$ and $D \le p + k$. Then every state in the frontier of $s$ cut at
depth $k$ is terminal.
