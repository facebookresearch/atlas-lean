# Multivalued and join dependencies; 4NF

This node collects multivalued and join dependencies and the normal forms based on them, over a relation
schema $U$.

## Expansion

A sound expansion has separate pages for:

1. **Definitions.** A multivalued dependency $X \twoheadrightarrow Y$ holds in $r$ over $U$ when
   $r = \pi_{XY}(r) \bowtie \pi_{X(U \setminus Y)}(r)$; a join dependency $\bowtie[R_1, \dots, R_n]$ with
   $R_1 \cup \dots \cup R_n = U$ holds when $r$ equals the join of its projections onto the $R_i$.
2. **Binary decompositions.** A decomposition $\{R_1, R_2\}$ with $R_1 \cup R_2 = U$ is lossless for every
   instance satisfying a dependency set if and only if $R_1 \cap R_2 \twoheadrightarrow R_1$ follows from it
   (Fagin). Every functional dependency $X \to Y$ implies $X \twoheadrightarrow Y$; this is
   [Heath's theorem](../lossless-decomposition-and-normal-forms/join-project-eq-of-holds-in.md) for the
   decomposition $\{XY, X(U \setminus Y)\}$, and the case of functional dependencies alone is
   [Lossless binary decompositions](../lossless-decomposition-and-normal-forms/lossless-join-iff.md).
3. **Normal forms.** Fourth normal form and project-join normal form, as definitions.

## Depends on

- [Functional dependency](../functional-dependencies/fd.md)

## Related topics

- [Heath's theorem](../lossless-decomposition-and-normal-forms/join-project-eq-of-holds-in.md)

## Sources

- Foundations of Databases (Abiteboul, Hull, Vianu) — Abiteboul, Hull, Vianu; authors' free web edition (webdam.inria.fr/Alice), Definitions 8.3.1 and 8.3.2 (p. 170), Proposition 8.2.2, Definition 11.2.2 (4NF) and Exercise 11.6 (PJ/NF, p. 267). <http://webdam.inria.fr/Alice/pdfs/all.pdf>
