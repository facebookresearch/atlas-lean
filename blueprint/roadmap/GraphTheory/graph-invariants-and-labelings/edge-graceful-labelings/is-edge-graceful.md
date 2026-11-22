# Edge-graceful graph

A simple graph $G$ on a finite vertex set $V$ is edge-graceful when
there are a natural number $q$ and a bijection $\ell$ from the edge set of $G$ to
$\{0, \dots, q-1\}$ such that the induced residue map, sending each vertex $v$ to the sum of
$\ell(e) + 1$ over the edges $e$ containing $v$ taken modulo $|V|$, is a bijection from $V$ to
$\{0, \dots, |V| - 1\}$.
