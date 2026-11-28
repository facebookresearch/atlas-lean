# Residual finite-dimensionality of free hypergraph C*-algebras is undecidable

No algorithm decides, given a finite hypergraph, whether its free hypergraph C*-algebra is residually finite-dimensional, that is, whether its finite-dimensional representations separate its elements.

**Theorem (Fritz).** There is no algorithm to determine, for a given finite hypergraph $H$, whether $C^*(H)$ is residually finite-dimensional.

Here a C\*-algebra is residually finite-dimensional if for every nonzero element there is a finite-dimensional representation that does not annihilate it. Fritz shows that the Connes embedding problem has a positive answer exactly when one particular free hypergraph C\*-algebra, that of Figure 2 of the source, is residually finite-dimensional (Proposition 2.13). Since [the Connes embedding conjecture is false](../../../../QuantumInformation/quantum-foundations/tsirelson-problem-and-connes-embedding/refutation-of-the-connes-embedding-conjecture.md) (Ji, Natarajan, Vidick, Wright and Yuen), that algebra is not residually finite-dimensional. Fritz (2020) leaves open whether residual finite-dimensionality of $C^*(H)$ is semi-decidable.

## Depends on

- [Free hypergraph C*-algebras](free-hypergraph-c-star-algebra.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Whether a free hypergraph C*-algebra is zero is undecidable](nontriviality-of-free-hypergraph-c-star-algebras.md)

## Expansion

If residual finite-dimensionality were decidable, one could decide $C^*(H) = 0$: when $C^*(H)$ is residually finite-dimensional, the norm of every polynomial in the generators is computable by the algorithm of Fritz, Netzer and Thom, so one can tell whether $\|1\| = 1$ or $\|1\| = 0$; when it is not residually finite-dimensional, it is in particular nonzero. A good expansion adds and links a page for the computability of norms in residually finite-dimensional finitely presented C\*-algebras (Fritz, Netzer and Thom).

## Sources

- Tobias Fritz, "Curious properties of free hypergraph C*-algebras", *Journal of Operator Theory* 83(2), 2020, pp. 423–445, <https://doi.org/10.7900/jot.2018oct18.2240>; read as arXiv:1808.09220v3, <https://arxiv.org/abs/1808.09220v3>: Theorem 3.4 and its proof, in the paragraph "Residual finite-dimensionality" of Section 3, and Proposition 2.13 (the Connes embedding problem and the algebra of Figure 2), of that version.
- Tobias Fritz, Tim Netzer and Andreas Thom, "Can you compute the operator norm?", *Proceedings of the American Mathematical Society* 142(12), 2014, pp. 4265–4276, <https://doi.org/10.1090/S0002-9939-2014-12170-8> (cited after the paper above, for the norm algorithm).
- Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright and Henry Yuen, "MIP* = RE", *Communications of the ACM* 64(11), 2021, pp. 131–138, <https://doi.org/10.1145/3485628> for the negative answer to the Connes embedding problem, which postdates the version of the paper above.
