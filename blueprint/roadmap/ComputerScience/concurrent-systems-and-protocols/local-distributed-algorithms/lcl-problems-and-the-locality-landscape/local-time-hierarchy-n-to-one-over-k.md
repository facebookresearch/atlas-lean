# A LOCAL time hierarchy: complexities n^(1/k) for every k

For every positive integer $k$ there is an LCL problem, $k$-level hierarchical $2\tfrac12$-colouring, whose deterministic and randomized LOCAL complexities are both $\Theta(n^{1/k})$, on bounded-degree trees as well as on general bounded-degree graphs. Moreover, on general bounded-degree graphs there are no LCL problems with deterministic complexity strictly between $\omega(\log^* n)$ and $o(\log n)$, while there exist LCL problems with deterministic complexity $\Theta(\log^{r/s} n)$ for all positive integers $r \ge s$, $\Theta(n^{r/s})$ for all positive integers with $r/s < 1/2$, and infinitely many deterministic complexities between $\omega(\sqrt n)$ and $o(n)$; on bounded-degree trees, by contrast, every LCL with complexity $o(n)$ has complexity $O(\sqrt n)$.

## Proof sketch

Hierarchical $2\tfrac12$-colouring lets vertices at level $i$ of a tree decomposition either output a proper $2$-colouring along long paths or declare themselves exempt; solving level $i$ quickly requires solving level $i - 1$ on paths of length about $n^{1/k}$, which gives matching upper and lower bounds by induction. The polylogarithmic and small polynomial complexities come from augmenting a cycle problem with layers of shortcuts whose lengths follow the register values of a simple register machine, which compresses distances along the cycle by a controlled amount; the complexities between $\sqrt n$ and $n$ come from LCLs whose valid instances encode executions of linear bounded automata, with complexity governed by the automaton's running time.

## Depends on

- [Deterministic and randomized LOCAL complexity of an LCL problem](lcl-deterministic-randomized-complexity.md)

## Proof depends on

- [Deterministic LCL complexities between log-star and log n collapse](lcl-deterministic-gap-log-star-log-n.md)

## Sources

- Y.-J. Chang, S. Pettie, "A Time Hierarchy Theorem for the LOCAL Model", FOCS 2017; SIAM Journal on Computing 48(1) (2019), arXiv:1704.06297, abstract.
- A. Balliu, J. Hirvonen, J. H. Korhonen, T. Lempiäinen, D. Olivetti, J. Suomela, "New Classes of Distributed Time Complexity", STOC 2018, arXiv:1711.01871, Table 2.
- A. Balliu, S. Brandt, D. Olivetti, J. Suomela, "Almost Global Problems in the LOCAL Model", DISC 2018; Distributed Computing 34 (2021), arXiv:1805.04776, abstract.
