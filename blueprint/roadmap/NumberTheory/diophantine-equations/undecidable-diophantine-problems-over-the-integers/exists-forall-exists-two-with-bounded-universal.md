# Diophantine sentences over the natural numbers with prefix ∃∀∃² and a bounded universal quantifier are undecidable

No algorithm decides, for a polynomial with integer coefficients, the truth over the natural numbers of sentences with quantifier prefix $\exists \forall \exists \exists$ in which the universal quantifier is bounded; from this one obtains undecidability with polynomials in four variables.

A sentence with prefix $\exists \forall \exists^2$ over $\mathbb{N}$ has the form $\exists u\, \forall x\, \exists y\, \exists z\ [f(u, x, y, z) = 0]$ for a polynomial $f$ with integer coefficients, all variables ranging over $\mathbb{N}$; in the bounded version the universal quantifier has explicit lower and upper bounds that are polynomials in the prior variables (the survey's notion of a bounded quantifier, Notation 7.1), given with integer coefficients as part of the input together with $f$. Matiyasevich showed that $\exists \forall \exists^2$, with $\forall$ bounded, over $\mathbb{N}$ is undecidable, and from this result one obtains undecidability with polynomials of four variables (Section 7.1 of the survey read).

The survey compares this with purely existential sentences, for which the best known number of unknowns is $9$ over $\mathbb{N}$.

## Depends on

- [Hilbert's tenth problem over a ring](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/hilbert-s-tenth-problem-over-a-ring.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The survey does not reproduce the proof. A full expansion links pages for Matiyasevich's arithmetical representation of every recursively enumerable set with this prefix and for a recursively enumerable set that is not decidable.

## Sources

- Yu. V. Matiyasevich, "Arithmetical representations of enumerable sets with a small number of quantifiers", Journal of Soviet Mathematics 6 (1976), no. 4, 410–416 (translation of the 1972 Russian original), https://doi.org/10.1007/BF01084081; cited for attribution beside the survey below, not read.
- W. Gasarch, "Hilbert's Tenth Problem: Refinements and Variants", survey, arXiv:2104.07220v1, 2021, <https://arxiv.org/abs/2104.07220v1>, a long version of the author's "Hilbert's Tenth Problem for Fixed d and n", Bulletin of the EATCS 133 (2021); read as arXiv:2104.07220v1 (Section 7.1, "Different Quantifier Prefixes", and Notation 7.1, in that version's numbering).
