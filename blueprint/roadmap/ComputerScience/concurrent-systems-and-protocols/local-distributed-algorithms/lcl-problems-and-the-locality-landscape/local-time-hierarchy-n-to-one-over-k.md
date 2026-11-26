# A LOCAL time hierarchy: complexities n^(1/k) for every k

For every positive integer $k$ there is an LCL problem on bounded-degree trees, $k$-level hierarchical $2\tfrac12$-colouring, whose deterministic and randomized LOCAL complexities are both $\Theta(n^{1/k})$. Moreover, on general bounded-degree graphs there are no LCL problems with deterministic complexity strictly between $\omega(\log^* n)$ and $o(\log n)$, while there exist LCL problems with complexity $\Theta(\log^{\alpha} n)$ for a dense set of exponents $\alpha \ge 1$ and complexity $\Theta(n^{\alpha})$ for a dense set of $\alpha \in (0, 1]$.

## Proof sketch

Hierarchical $2\tfrac12$-colouring lets vertices at level $i$ of a tree decomposition either output a proper $2$-colouring along long paths or declare themselves exempt; solving level $i$ quickly requires solving level $i - 1$ on paths of length about $n^{1/k}$, which gives matching upper and lower bounds by induction. The dense families of exponents are obtained by encoding the behaviour of linear bounded automata or counters into LCL problems on grids or trees whose solution requires propagating information over distances with the desired growth.

## Depends on

- [Deterministic and randomized LOCAL complexity of an LCL problem](lcl-deterministic-randomized-complexity.md)

## Proof depends on

- [Deterministic LCL complexities between log-star and log n collapse](lcl-deterministic-gap-log-star-log-n.md)

## Sources

- Y.-J. Chang, S. Pettie, "A Time Hierarchy Theorem for the LOCAL Model", FOCS 2017; SIAM Journal on Computing 48(1) (2019), arXiv:1704.06297.
- A. Balliu, J. Hirvonen, J. H. Korhonen, T. Lempiäinen, D. Olivetti, J. Suomela, "New Classes of Distributed Time Complexity", STOC 2018, arXiv:1711.01871.
- A. Balliu, S. Brandt, D. Olivetti, J. Suomela, "Almost Global Problems in the LOCAL Model", DISC 2018; Distributed Computing 34 (2021), arXiv:1805.04776.
