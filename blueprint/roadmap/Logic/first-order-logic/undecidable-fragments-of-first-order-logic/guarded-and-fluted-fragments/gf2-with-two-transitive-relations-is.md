# The two-variable guarded fragment with two transitive relations is undecidable

Satisfiability and finite satisfiability are undecidable for two-variable guarded formulas in which two binary symbols must denote transitive relations, as soon as these symbols may occur outside guards.

**Theorem (Kieroński).** For the [two-variable guarded fragment](two-variable-guarded-fragment.md) $\mathrm{GF}^2$ extended with two special binary symbols interpreted as transitive relations, both the satisfiability problem and the finite satisfiability problem are undecidable.

The overview in Kieroński and Tendera also credits Kazakov (doctoral thesis, 2006) with this result. With a single transitive relation both problems are 2ExpTime-complete (satisfiability: Kieroński; finite satisfiability: Kieroński and Tendera). With any number of transitive relations that occur only as guards, satisfiability is 2ExpTime-complete (Szwast and Tendera; Kieroński).

## Depends on

- [Two-variable guarded fragment](two-variable-guarded-fragment.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The tiling problem is undecidable](../../../../TheoryOfComputation/undecidable-problems/wang-tiles/the-tiling-problem-is-undecidable.md)

## Expansion

Kazakov's proof (Theorem 5.1.2 of his thesis) reduces domino problems: a $\mathrm{GF}^2$ formula GRID over two transitive relations $S$ and $T$, interleaving edges of the two sorts and alternating their directions so that distant nodes are not connected, forces a grid with horizontal and vertical relations, and its conjunction with the tiling conditions is satisfiable iff the domino system tiles the grid and finitely satisfiable iff it tiles it periodically. A good expansion links the tiling problem, the undecidability of periodic tiling that finite satisfiability needs, and a page for the grid formula. The decidability of an extension depends on the number and kind of special relations, and on whether they may occur outside guards.

## Sources

- E. Kieroński, "Results on the guarded fragment with equivalence or transitive relations", in *Computer Science Logic (CSL 2005)*, Lecture Notes in Computer Science 3634, Springer, 2005, pp. 309–324, doi:[10.1007/11538363_22](https://doi.org/10.1007/11538363_22) (original source, cited as recalled in the overview of Kieroński and Tendera).

- E. Kieroński and L. Tendera, "Finite satisfiability of the two-variable guarded fragment with transitive guards and related variants", *ACM Transactions on Computational Logic* 19(2), Article 8, 2018, doi:[10.1145/3174805](https://doi.org/10.1145/3174805). Numbering of the version read, arXiv:1611.03267v3: Section 1 and Table I (rows "2 transitive r." and "1 transitive r.").
- Y. Kazakov, *Saturation-based decision procedures for extensions of the guarded fragment*, doctoral thesis, Universität des Saarlandes, 2006; read in the author's copy at <https://www.cs.ox.ac.uk/people/yevgeny.kazakov/publications/thesis/Kazakov06phd.pdf>: Section 3.4 (domino problems) and Section 5.1.3 with Figure 5.3 and Theorem 5.1.2.
