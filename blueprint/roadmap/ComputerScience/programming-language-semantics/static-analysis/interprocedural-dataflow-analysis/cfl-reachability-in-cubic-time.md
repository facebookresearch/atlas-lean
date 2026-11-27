# CFL-reachability in cubic time

Fix a context-free grammar for a language $L$. The all-pairs [CFL-reachability](context-free-language-reachability.md) problem for $L$ on a graph with $n$ nodes can be solved in time $O(n^3)$. After normalizing the grammar so that every right-hand side has at most two symbols, the algorithm adds an edge labeled $A$ from $x$ to $y$ for each production $A \to \varepsilon$ with $x = y$, each production $A \to B$ and edge $x \xrightarrow{B} y$, and each production $A \to B\,C$ and edges $x \xrightarrow{B} z \xrightarrow{C} y$, until no edge can be added; the $L$-paths are the edges labeled with the start symbol. With a worklist and suitable indexing the saturation takes cubic time.

## Depends on

- [Context-free-language reachability](context-free-language-reachability.md)

## Sources

- T. Reps, "Program analysis via graph reachability", *Information and Software Technology* 40(11–12):701–726, 1998, doi:10.1016/S0950-5849(98)00093-7, author copy <https://research.cs.wisc.edu/wpis/papers/tr1386.pdf>, Section 3: the normalization of the grammar, the edge-addition patterns of Figure 2, and the cubic bound, which Reps credits to D. Melski and T. Reps, "Interconvertibility of set constraints and context-free language reachability", PEPM 1997.
