# Edge expansion of a vertex set

Let $G$ be a simple graph on a finite vertex set $V$ and
let $S \subseteq V$ be nonempty. Let $d$ be the degree in $G$ of a fixed vertex of $S$, chosen
once for each $S$. The expansion of $S$ is the rational number
$\Phi_G(S) = |E(S, V \setminus S)| / (d \cdot |S|)$, where $E(S, V \setminus S)$ is the set of
edges of $G$ with one endpoint in $S$ and the other in $V \setminus S$; it is $0$ when $d = 0$.

For a $d$-regular graph, $d$ is the common degree and this is Definition 1.8 of Khot, Minzer and
Safra, which also asks that $|S| \le |V|/2$; neither regularity nor that bound is assumed here.
