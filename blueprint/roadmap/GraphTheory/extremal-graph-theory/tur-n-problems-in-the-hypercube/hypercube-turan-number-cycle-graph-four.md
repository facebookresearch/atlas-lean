# Four-cycle-free subgraphs of the hypercubes of dimensions one to six

For a natural
number $n$, let $Q_n$ be the $n$-dimensional hypercube, let $C_4$ be the cycle on four vertices,
and let $\mathrm{ex}(Q_n, C_4)$ be the largest number of edges of a subgraph of $Q_n$ that
contains no copy of $C_4$. Then for $n = 1, 2, 3, 4, 5, 6$ the value of $\mathrm{ex}(Q_n, C_4)$
is $1$, $3$, $9$, $24$, $56$ and $132$ respectively.

## Sources

- OEIS A245762; `ex(Q₆, C₄) = 132` is H. Harborth and H. Nienborg, *Maximum number of edges in squarefree subgraphs of the n-cube*, Bull. Inst. Combin. Appl. 12 (1994), 55–60; listed in leansolving/SqueezeBench `SqueezeBench/Problems/HypercubeC4/README.md`.
- Minamo Minamoto, [six-cube witness data](https://github.com/minamominamoto/c4free-hypercube/blob/918025df85b509c4311675e0d1ba65f26f23d98d/q6_odd_square_132.json), described in [arXiv:2603.29127v5](https://arxiv.org/html/2603.29127v5). Restricting this witness to coordinate faces gives the lower bounds in dimensions one through five.
