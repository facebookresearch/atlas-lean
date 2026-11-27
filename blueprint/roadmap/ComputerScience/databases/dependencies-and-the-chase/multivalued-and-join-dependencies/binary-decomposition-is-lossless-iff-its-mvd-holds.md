# A binary decomposition is lossless exactly when its multivalued dependency holds

Let $U$ be a finite set of attributes and $R_1, R_2 \subseteq U$ with $R_1 \cup R_2 = U$. For every relation $I$ over $U$,

$$I = \pi_{R_1}(I) \bowtie \pi_{R_2}(I) \iff I \models R_1 \cap R_2 \twoheadrightarrow R_1 \setminus R_2 .$$

Consequently the decomposition $\{R_1, R_2\}$ is lossless on every instance satisfying a set $\Sigma$ of dependencies if and
only if $\Sigma$ implies $R_1 \cap R_2 \twoheadrightarrow R_1 \setminus R_2$. Every functional dependency $X \to Y$ implies the
multivalued dependency $X \twoheadrightarrow Y$; for decompositions justified by functional dependencies this is
[Heath's theorem](../../lossless-decomposition-and-normal-forms/join-project-eq-of-holds-in.md).

## Depends on

- [Join dependencies and multivalued dependencies](join-dependencies-and-multivalued-dependencies.md)
- [Functional dependency](../../functional-dependencies/fd.md)

## Proof depends on

- [Heath's theorem](../../lossless-decomposition-and-normal-forms/join-project-eq-of-holds-in.md)
- [Lossless binary decompositions](../../lossless-decomposition-and-normal-forms/lossless-join-iff.md)

## Sources

- S. Abiteboul, R. Hull and V. Vianu, *Foundations of Databases*, Addison-Wesley, 1995; authors' web edition <http://webdam.inria.fr/Alice/pdfs/all.pdf>, Definitions 8.3.1 and 8.3.2 (p. 170), Proposition 8.2.2 (p. 164) and rule FMVD1 of Theorem 8.3.5 (p. 172).
- R. Fagin, "Multivalued dependencies and a new normal form for relational databases", *ACM Trans. Database Syst.* 2(3) (1977) 262–278, where multivalued dependencies are introduced as the condition for a lossless decomposition into two projections.
