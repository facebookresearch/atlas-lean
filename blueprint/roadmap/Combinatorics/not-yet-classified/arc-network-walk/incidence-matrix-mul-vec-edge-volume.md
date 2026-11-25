# Node balance of route edge volumes

Let a network have finitely many nodes and arcs $e$ with tails and heads, and finitely many routes $p$, each a list of arcs forming a walk from its origin to its destination, with flow $f_p \in \mathbb R$. Let the edge volume of $e$ be $\sum_p f_p$ times the number of traversals of $e$ by $p$, and let $B_{ve} = [\mathrm{head}(e) = v] - [\mathrm{tail}(e) = v]$ be the incidence matrix. Then for every node $v$,

$$(B\,\mathrm{vol})_v = \sum_p f_p\left([\mathrm{dest}(p) = v] - [\mathrm{orig}(p) = v]\right).$$
