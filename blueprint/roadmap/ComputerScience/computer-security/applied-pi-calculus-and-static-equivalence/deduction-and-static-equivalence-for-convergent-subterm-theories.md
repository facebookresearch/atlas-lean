# Deduction and static equivalence are polynomial for convergent subterm theories

**Theorem (Abadi and Cortier).** Let $E$ be a [convergent subterm theory](equational-theories-and-convergent-subterm-theories.md). For all closed frames $\varphi$ and $\varphi'$ (frames whose substituted terms are closed) and every
closed term $M$, it is decidable in time polynomial in the sizes of $\varphi$, $\varphi'$ and $M$ whether $M$ is deducible from $\varphi$ and whether
$\varphi \approx_s \varphi'$ ([static equivalence](frames-and-static-equivalence.md)).

The polynomial bound uses DAG representations of terms. The restriction to a class of theories matters: there are equational theories for which deduction is undecidable.

## Depends on

- [Frames and static equivalence](frames-and-static-equivalence.md)
- [The complexity class P](../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/p.md)

## Sources

- M. Abadi and V. Cortier, "Deciding knowledge in security protocols under equational theories", *Theoretical Computer Science* 367(1–2), 2006; preprint of 18 October 2005 at <https://members.loria.fr/VCortier/files/Papers/AbadiCortierTCS06.pdf>: Section 4.3, Theorem 1 and its proof; Proposition 3 (an equational theory with undecidable deduction).
