# Depth budget bounds the depth-first stack size

Let $D, T, q \in \mathbb{N}$ and let $G(s, p, t)$ be a relation between states and natural numbers
such that $G(s, p, t)$ implies $p \le D$ and $t \le T$, and such that if $G(s, p, t)$ and $s$
branches into $(l, h)$ then $G(l, p + 1, t)$ and $G(h, p + 1, t + q)$. Let $s$ be a state with
$G(s, p, t)$. Then for every $i \in \mathbb{N}$, after $i$ depth-first rounds from the pair
(stack $[s]$, empty output), the stack has length at most $D + 1$, and every state $x$ on it
satisfies $G(x, p', t')$ for some $p', t'$.
