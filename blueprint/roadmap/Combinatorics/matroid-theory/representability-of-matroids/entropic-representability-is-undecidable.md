# Entropic and almost multilinear representability of matroids are undecidable

No algorithm decides whether a given finite matroid is entropic, that is, whether its rank function is a positive multiple of the joint entropy function of some discrete random variables; nor whether it is almost multilinear, approximately representable by subspace arrangements.

Let $M$ range over finite matroids, given by their rank functions, and let entropic and almost multilinear matroids be as in [matroids and their representations](matroid-representations.md).

**Theorem (Kühne and Yashfe).**

1. The *entropic matroid representation problem*, which asks, given a matroid $M$, whether $M$ is entropic, is undecidable (Theorems 1.2 and 7.3 of arXiv:2206.03465v3).
2. It is undecidable, given a matroid $M$, whether $M$ is almost multilinear (Theorem 1.4 and Corollary 9.18 of arXiv:2206.03465v3).

Entropic matroids are exactly the secret sharing matroids of Brickell and Davenport, so clause 1 shows that it is undecidable which connected monotone access structures admit an ideal secret sharing scheme, a question of Martin. As a corollary, the source obtains that the conditional independence implication problem for discrete random variables is undecidable (Corollary 1.6 and Theorem 8.5), a result proved independently by Cheuk Ting Li. In the introduction of the source the almost multilinear problem takes a matroid together with a field; Corollary 9.18 concerns almost multilinearity with respect to linear polymatroids over arbitrary fields. Linear representability over some field is decidable, and [multilinear representability](multilinear-representability-is-undecidable.md) and [skew-linear representability](skew-linear-representability-is-undecidable.md) are undecidable as well.

## Depends on

- [Matroids and their representations over division rings, by subspaces and by random variables](matroid-representations.md)

## Proof depends on

None.

## Expansion

Both clauses reduce word problems for finitely presented groups to the representability of finite families of partial Dowling geometries built from a symmetric triangular presentation. For clause 1, if the group has a finite quotient in which a given generator is nontrivial, permutation representations give a multilinear, hence entropic, member of the family (Theorem 7.1); conversely an entropic member yields a homomorphism to a symmetric group separating the generator from the identity (Theorems 4.5 and 7.2), so the uniform word problem for finite groups, undecidable by Slobodskoi, reduces to entropic representability. For clause 2, approximate representations of sofic groups in rank distance give almost multilinear members (Theorem 9.16), and almost multilinear members force the generator to be nontrivial (Theorem 9.17); the word problem of a finitely presented torsion-free sofic group with undecidable word problem (Theorem 2.11) then reduces to almost multilinearity. A good expansion links Slobodskoi's undecidability of the uniform word problem for finite groups and the existence of a finitely presented sofic group with undecidable word problem, which have no pages.

## Sources

- L. Kühne and G. Yashfe, "On entropic and almost multilinear representability of matroids", *Duke Mathematical Journal* 175 (2026), no. 8, 1363–1451, doi:10.1215/00127094-2025-0047; read as arXiv:2206.03465v3, <https://arxiv.org/abs/2206.03465v3>: Problem 1.3, Theorems 1.2, 1.4, 2.9, 2.11, 4.5, 7.1, 7.2, 7.3, 8.5, 9.16 and 9.17, Corollaries 1.6 and 9.18, and Definitions 2.3 and 2.4, in the numbering of arXiv:2206.03465v3.
