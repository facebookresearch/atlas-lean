# Layered digraphs and min-isolating weights

A **layered digraph** on the vertex set $\{0, \dots, n\} \times \{0, \dots, w-1\}$ (layer, column) is a digraph every arc of which goes from some layer $i$ to layer $i + 1$. A **vertex weight assignment** is $\mathrm{wt} : V \to \mathbb{N}$, and the weight of a path is the sum of the weights of its internal vertices. The assignment is **min-isolating** for $G$ if for every pair $(u, v)$ with $v$ reachable from $u$ there is a unique $u$-$v$ path of minimum weight.

## Depends on

- [Isolation lemma](../../../../Combinatorics/probabilistic-combinatorics/isolation-lemma.md)
- [The complexity class NL](../../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/nl.md)

## Sources

- W. M. Hoza, "NL = UL", Electronic Colloquium on Computational Complexity, Report TR26-323, 2026.
- K. Reinhardt and E. Allender, "Making Nondeterminism Unambiguous", SIAM Journal on Computing 29(4), 2000.
