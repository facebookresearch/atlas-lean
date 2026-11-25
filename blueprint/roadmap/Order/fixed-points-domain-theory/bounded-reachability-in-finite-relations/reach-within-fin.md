# Reach Within Fin

Let $\alpha$ be a finite set, $r$ a decidable binary relation on $\alpha$ and $a \in \alpha$. The rounds $N_k(a) \subseteq \alpha$ are defined by

$$N_0(a) = \{a\}, \qquad N_{k+1}(a) = N_k(a) \cup \{ t \in \alpha : r(z, t) \text{ for some } z \in N_k(a) \}.$$

Thus $N_k(a)$ is the set of elements reachable from $a$ in at most $k$ steps of $r$.
