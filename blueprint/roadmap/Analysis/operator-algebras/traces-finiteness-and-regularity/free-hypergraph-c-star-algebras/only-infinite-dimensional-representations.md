# Having only infinite-dimensional representations is undecidable for free hypergraph C*-algebras

Some finite hypergraphs have quantum representations only in infinite-dimensional Hilbert spaces, and no algorithm decides, given a hypergraph, whether its free hypergraph C*-algebra is nonzero but has no finite-dimensional representation.

**Theorem (Fritz).** There are finite hypergraphs $H$ such that $C^*(H)$ is nonzero but has no finite-dimensional representation. Moreover, there is no algorithm to determine, for a given $H$, whether this is the case.

So there are finite configurations of closed subspaces, pairwise orthogonal and spanning along prescribed subsets, that can be realized only in infinite-dimensional Hilbert spaces. Fritz (2020) leaves open whether the problem is semi-decidable.

## Depends on

- [Free hypergraph C*-algebras](free-hypergraph-c-star-algebra.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Whether a free hypergraph C*-algebra is zero is undecidable](nontriviality-of-free-hypergraph-c-star-algebras.md)

## Expansion

The proof follows the one for residual finite-dimensionality. Given an oracle for the property, decide $C^*(H) = 0$ as follows. Ask the oracle whether $C^*(H)$ is nonzero with no finite-dimensional representation; if it is, answer nonzero. Otherwise $C^*(H)$ is zero or has a finite-dimensional representation, and the operator-norm algorithm of Fritz, Netzer and Thom decides whether $\|1\| = 1$ or $\|1\| = 0$: if $\|1\| = 1$, this norm is attained in any finite-dimensional representation, which suffices for that algorithm. The existence of such $H$ follows from the undecidability.

A good expansion adds and links a page for the operator-norm algorithm of Fritz, Netzer and Thom.

## Sources

- Tobias Fritz, "Curious properties of free hypergraph C*-algebras", *Journal of Operator Theory* 83(2), 2020, pp. 423–445, <https://doi.org/10.7900/jot.2018oct18.2240>; read as arXiv:1808.09220v3, <https://arxiv.org/abs/1808.09220v3>: Theorem 3.5 and its proof, in the paragraph "Infinite-dimensional representations" of Section 3 of that version.
- Tobias Fritz, Tim Netzer and Andreas Thom, "Can you compute the operator norm?", *Proceedings of the American Mathematical Society* 142(12), 2014, pp. 4265–4276, <https://doi.org/10.1090/S0002-9939-2014-12170-8> (cited after the paper above).
