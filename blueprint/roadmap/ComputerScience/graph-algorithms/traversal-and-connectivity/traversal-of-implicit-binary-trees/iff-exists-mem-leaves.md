# Branch-split properties hold at the root iff at some leaf

Let $q \in \mathbb{N}$ and let $G(s, p, t)$ be a relation between states and natural numbers such
that if $G(s, p, t)$ and $s$ branches into $(l, h)$, then $G(l, p + 1, t)$ and
$G(h, p + 1, t + q)$. Let $P$ be a property of states such that whenever $G(s, p, t)$ holds and
$s$ branches into $(l, h)$, $P(s)$ holds if and only if $P(l)$ or $P(h)$ holds. Then for every
depth $k$ and every state $s$ with $G(s, p, t)$, $P(s)$ holds if and only if $P(x)$ holds for some
state $x$ in the frontier of $s$ cut at depth $k$.
