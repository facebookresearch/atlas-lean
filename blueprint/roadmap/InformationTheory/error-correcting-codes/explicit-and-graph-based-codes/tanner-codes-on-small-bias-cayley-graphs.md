# Tanner codes on small-bias Cayley graphs of the cube

Let $s_1, \dots, s_d \in \mathbb{F}_2^\ell$ be $\varepsilon$-biased generators ($\varepsilon \ge 0$) and consider the bipartite double cover of their Cayley graph: left vertex $u$ is joined by its port-$j$ edge to right vertex $u + s_j$, so there are $2^\ell d$ edges. Let the local code be the kernel of a $c \times d$ binary matrix $A$, and suppose every nonzero word of length $d$ in this kernel has weight greater than $h$; such an $A$ exists whenever fewer than $2^c$ nonzero words of length $d$ have weight at most $h$. Then every nonzero Tanner word $x$ (bits on edges, local word in $\ker A$ at every left and right vertex) satisfies

$$(h + 1)(h + 1 - \varepsilon d)\, 2^\ell \le d \cdot \mathrm{wt}(x).$$

## Proof sketch

The existence of $A$ is a union bound: a fixed nonzero word lies in the kernel of exactly a $2^{-c}$ fraction of all $c \times d$ matrices. For the distance, the vertices touching the support of $x$ on each side see at least $h + 1$ support edges, and the expander mixing bound for the Cayley graph, whose spectral expansion is at most $\varepsilon$, limits the edges between the two touched sets, which gives the inequality.

## Depends on

- [Bipartite Tanner codes on regular bipartite multigraphs](bipartite-tanner-code.md)
- [Cayley graphs of the Boolean cube with small-bias generators are expanders](../../../GraphTheory/graph-families-and-operations/explicit-and-random-expander-constructions/small-bias-cayley-graphs-of-the-cube.md)

## Proof depends on

- [Cayley graphs of the Boolean cube with small-bias generators are expanders](../../../GraphTheory/graph-families-and-operations/explicit-and-random-expander-constructions/small-bias-cayley-graphs-of-the-cube.md)
- [Expander mixing lemma](../../../GraphTheory/graph-families-and-operations/expander-graphs/expander-mixing-lemma.md)

## Sources

- R. M. Tanner, "A Recursive Approach to Low Complexity Codes", IEEE Transactions on Information Theory, 1981.
- M. Sipser, D. A. Spielman, "Expander Codes", IEEE Transactions on Information Theory, 1996.
