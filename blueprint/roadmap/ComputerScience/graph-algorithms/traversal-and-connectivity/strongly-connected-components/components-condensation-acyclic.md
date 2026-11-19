# The condensation of the computed components is acyclic

Let $G$ be a directed graph and
let $S$ and $T$ be blocks returned by the strongly connected components algorithm on $G$. If some
vertex of $S$ reaches some vertex of $T$ and some vertex of $T$ reaches some vertex of $S$, then
$S = T$.

Equivalently, the condensation relation has no nontrivial directed cycle.
