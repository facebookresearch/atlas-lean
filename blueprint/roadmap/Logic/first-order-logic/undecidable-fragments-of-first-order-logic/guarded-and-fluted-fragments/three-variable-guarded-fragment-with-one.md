# The three-variable guarded fragment with one functional relation is undecidable

Already with three variables, the guarded fragment becomes undecidable when one binary relation is required to be functional.

**Theorem (Grädel).** Satisfiability for the three-variable [guarded fragment](guarded-fragment.md) $\mathrm{GF}^3$ extended by one functional relation, a distinguished binary relation symbol that must denote a partial function, is undecidable, and so is its finite satisfiability.

By contrast, the two-variable guarded fragment extended by number restrictions, which generalize functionality, remains decidable (Kazakov gives a polynomial translation of it into $\mathrm{GF}$).

## Depends on

- [Guarded fragment of first-order logic](guarded-fragment.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

Grädel proves more: $\mathrm{GF}^3$ without equality together with one functionality statement is a conservative reduction class (Theorem 5.8 of the author's copy), so satisfiability and finite satisfiability are both undecidable. The proof expands finite grids by ternary relations composed of the horizontal and vertical successors, which serve as guards, and characterizes grids in the sense of Lemma 5.7; Theorem 5.6 then applies, which uses that the domino systems admitting a periodic tiling of $\mathbb N \times \mathbb N$ and those admitting no tiling are recursively inseparable (Gurevich and Koryakov). A good expansion links pages for this inseparability, for Theorem 5.6 and for the grid characterization. Functionality and transitivity are the two features of expressive modal and description logics that lie outside the guarded fragment; for transitivity, see [the two-variable guarded fragment with two transitive relations](gf2-with-two-transitive-relations-is.md).

## Sources

- E. Grädel, "On the restraining power of guards", *Journal of Symbolic Logic* 64(4):1719–1742, 1999, doi:10.2307/2586808; read in the author's copy at <https://logic.rwth-aachen.de/pub/graedel/Gr-jsl99.ps>, whose numbering is used here: Section 5.1 (Theorem 5.6, Lemma 5.7) and Theorem 5.8.
- Y. Kazakov, "A polynomial translation from the two-variable guarded fragment with number restrictions to the guarded fragment", in *Logics in Artificial Intelligence (JELIA 2004)*, Lecture Notes in Computer Science 3229, Springer, 2004, pp. 372–384, doi:10.1007/978-3-540-30227-8_32; read in the author's open-access copy at <http://www.cs.ox.ac.uk/people/yevgeny.kazakov/publications/confs/Kaz04GF2N.pdf>: Section 1, which states the undecidability.
- B. Bednarczyk, M. Orłowska, A. Pacanowska and T. Tan, "On Classical Decidable Logics Extended with Percentage Quantifiers and Arithmetics", in *41st IARCS Annual Conference on Foundations of Software Technology and Theoretical Computer Science (FSTTCS 2021)*, Leibniz International Proceedings in Informatics 213, Schloss Dagstuhl, 2021, paper 36, <https://doi.org/10.4230/LIPIcs.FSTTCS.2021.36>; read as arXiv:2106.15250v2, <https://arxiv.org/abs/2106.15250v2>: the paragraph before Theorem 9, which states that finite satisfiability of this fragment is undecidable, citing Grädel.
