# Mem reach Within Fin succ

Let $\alpha$ be a finite set, $r$ a decidable binary relation on $\alpha$, $a \in \alpha$, and let $N_k(a)$ be the set of elements reachable from $a$ in at most $k$ steps of $r$ ($N_0(a) = \{a\}$). For every $t \in \alpha$ and $k \in \mathbb{N}$,

$$t \in N_{k+1}(a) \iff t \in N_k(a) \ \text{ or } \ r(z, t) \text{ for some } z \in N_k(a).$$
