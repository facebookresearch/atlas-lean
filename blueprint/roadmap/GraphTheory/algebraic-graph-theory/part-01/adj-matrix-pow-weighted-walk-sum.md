# Powers of a weighted adjacency matrix sum the weights of walks

Let $R$ be a commutative
semiring, let $k$ and $n$ be natural numbers, and let $A$ be a $k \times k$ matrix over $R$ with
rows and columns indexed by $\{0, \dots, k-1\}$, viewed as the weighted adjacency matrix of a
weighted digraph on these $k$ vertices. Then for all vertices $i$ and $j$,

$$(A^n)_{ij} = \sum_{p} \prod_{t=0}^{n-1} A_{p_t p_{t+1}},$$

where the sum runs over all sequences $p = (p_0, \dots, p_n)$ of vertices with $p_0 = i$ and
$p_n = j$, that is, over all walks of length $n$ from $i$ to $j$, each weighted by the product
of the entries of $A$ along its edges.

The source states $n \ge 1$; the case $n = 0$ is included, where both sides equal $1$ if
$i = j$ and $0$ otherwise.

## Sources

- Thomas Koshy, "A Graph-Theoretic Model for a Generalized Fibonacci Gem," Journal of Integer Sequences 22 (2019), Article 19.4.1, Theorem (label theorem01), lines 128–130, https://cs.uwaterloo.ca/journals/JIS/VOL22/Koshy/koshy7.tex
