# Walk in an arc network as a list of arcs

Let $V$ and $E$ be sets and let each arc $e \in E$ run from its tail $t(e) \in V$ to its head $h(e) \in V$. A list $[e_1, \dots, e_k]$ of arcs is a walk from $o \in V$ to $d \in V$ if it is empty only when $o = d$ and, when $k \ge 1$, $t(e_1) = o$, $h(e_i) = t(e_{i+1})$ for $1 \le i < k$, and $h(e_k) = d$. The empty list is thus a walk from $o$ to $d$ exactly when $o = d$. Arcs and vertices may repeat, and parallel arcs are told apart, since the walk records arcs rather than vertex pairs.
