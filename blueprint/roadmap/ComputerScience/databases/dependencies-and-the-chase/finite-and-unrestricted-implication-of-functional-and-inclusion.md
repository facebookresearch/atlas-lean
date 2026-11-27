# Finite and unrestricted implication of functional and inclusion dependencies

Fix a countably infinite value domain. On any one finite schema $S$, [finite implication](finitely-implies.md) and [unrestricted implication](implies.md) use the same [satisfaction relation](holds-in-2.md) for [schema dependencies](dependency.md).

- **Pure dependencies.** For every $S$, every set $F$ of FDs on $S$ and every FD $\sigma$ on $S$, $F\models_{\rm fin}\sigma$ if and only if $F\models_{\rm unr}\sigma$. The same equivalence holds for every $S$ when all the hypotheses and the conclusion are INDs.
- **Mixed dependencies.** There exist a finite schema $S$, a finite set $F$ of FDs and INDs on $S$, and a dependency $\sigma$ on $S$ for which $F\models_{\rm fin}\sigma$ but $F\not\models_{\rm unr}\sigma$.
- **Decision problems.** Given a finite schema $S$, a finite set $F$ of FDs and INDs on $S$, and a dependency $\sigma$ on $S$, no algorithm decides whether $F\models_{\rm fin}\sigma$. With the same input convention, no algorithm decides whether $F\models_{\rm unr}\sigma$. In both problems $S$ is part of the input.

## Proof outline

Unrestricted implication always gives finite implication. For the converse for FDs, collect the hypotheses on the conclusion's relation; its finite attribute set admits only finitely many distinct FDs. Embed the two Boolean values in the value domain and leave the other relations empty: any Boolean counterexample with at most two rows then gives a finite database counterexample. In its absence the two-tuple completeness theorem yields an Armstrong derivation, hence unrestricted validity. For INDs, finite completeness gives a derivation by IND1–IND3, each sound on arbitrary instances.

For separation, take one binary relation $R(A,B)$, hypotheses $A\to B$ and $R[A]\subseteq R[B]$, and conclusion $R[B]\subseteq R[A]$. The FD gives a surjection from the occurring $A$-values onto the occurring $B$-values. In a finite instance the inclusion in the other direction forces the two sets to be equal. But $R=\{(n+1,n):n\in\mathbb N\}$ satisfies the hypotheses and has $0$ in its second projection only.

Undecidability uses a different argument. A uniform reduction sends a finite list of word equations and a proposed equation to a schema and a mixed implication input. The unrestricted and finite monoid problems reduce to the corresponding database problems; a decision procedure for either database problem would decide its monoid counterpart.

## Depends on

- [Functional and inclusion dependencies on a schema](dependency.md)
- [Satisfaction of a schema dependency](holds-in-2.md)
- [Finite implication of dependencies](finitely-implies.md)
- [Unrestricted implication of dependencies](implies.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Unrestricted implication gives finite implication](finitely-implies-of-implies.md)
- [Completeness of Armstrong's axioms, two-tuple form](../functional-dependencies/derives-of-forall-two-tuple.md)
- [Armstrong's theorem](../functional-dependencies/derives-iff-entails.md)
- [Finite completeness of the inclusion dependency rules](implication-proofs/finite-ind-completeness.md)
- [Reflexivity of projection inclusion](holds-in-refl.md)
- [Projection and permutation of an inclusion dependency](implication-proofs/projection-and-permutation.md)
- [Transitivity of projection inclusion](holds-in-trans.md)
- [Word consequences over all monoids and over finite monoids](implication-proofs/monoid-word-consequences.md)
- [Reduction from monoid word consequences to mixed implication](implication-proofs/monoid-to-mixed-implication.md)
- [Decidability transfers along mapping reductions](../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/tm2-decidable-of-many-one-reducible.md)

## Sources

- S. Abiteboul, R. Hull and V. Vianu, [*Foundations of Databases*](https://webdam.di.ens.fr/Alice/pdfs/all.pdf), Addison-Wesley, 1995. Theorem 9.2.2 and Fig. 9.1(a) give the mixed witness; Theorem 9.2.3 gives pure coincidence; Theorem 9.2.4 gives the two undecidability results. For FDs alone the two-tuple argument also follows the completeness proof of Theorem 8.2.11; the book's proof of 9.2.3 invokes the tableau theorem 8.4.12 to cover join dependencies as well.
