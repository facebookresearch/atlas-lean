# Flow across a cut

Let $V$ be a finite set, $s, t \in V$, and
$f : V \times V \to \mathbb{R}$ a function conserved at every vertex $v \ne s, t$, that is,
$\sum_{u \in V} f(u, v) = \sum_{w \in V} f(v, w)$; no sign or capacity condition is imposed. Then
for every subset $S \subseteq V$ with $s \in S$ and $t \notin S$, the flow value
$\sum_{v \in V} f(s, v) - \sum_{u \in V} f(u, s)$ of $f$ equals
$\sum_{u \in S} \sum_{v \in V \setminus S} f(u, v) -
\sum_{u \in S} \sum_{v \in V \setminus S} f(v, u)$, the flow leaving $S$ minus the flow
entering $S$.
