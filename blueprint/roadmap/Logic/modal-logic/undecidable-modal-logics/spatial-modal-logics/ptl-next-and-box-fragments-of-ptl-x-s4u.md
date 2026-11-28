# The spatio-temporal logics PTL∘S4u and PTL□×S4u are undecidable

Satisfiability stays undecidable for the fragments of PTL × S4u in which terms may use only the next-time operator, or only "always in the future" and "always in the past", over the integers, the natural numbers or finite flows of time.

**Theorem (Gabelaia, Kontchakov, Kurucz, Wolter and Zakharyaschev).** For the logics of the page on [topological temporal models](spatio-temporal-logic-ptl-x-s4u.md):

1. the satisfiability problem for $\mathrm{PTL} \circ \mathrm{S4}_u$ formulas in tt-models based on the flows of time $(\mathbb N, <)$ or $(\mathbb Z, <)$ is undecidable, and it is undecidable as well for tt-models satisfying the finite state assumption or based on arbitrary finite flows of time (Theorem 3.6 of the source);
2. the satisfiability problem for $\mathrm{PTL}_\Box \times \mathrm{S4}_u$ formulas in tt-models, with or without the finite state assumption, based on the flows of time $(\mathbb N, <)$ or $(\mathbb Z, <)$ is undecidable, and it is undecidable as well for tt-models based on arbitrary finite flows of time (Theorem 3.7).

The proofs show that both statements already hold for the future fragments of the two languages. In $\mathrm{PTL} \circ \mathrm{S4}_u$ the state of a region can only be compared at boundedly many time points, and $\mathrm{PTL} \circ \mathrm{S4}_u$ formulas do not distinguish arbitrary tt-models from those based on Aleksandrov topological spaces; still the interaction of $\bigcirc$ with the interior operator suffices for undecidability.

## Depends on

- [Topological temporal models and the spatio-temporal logic PTL × S4u](spatio-temporal-logic-ptl-x-s4u.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The Post correspondence problem is undecidable](../../../../TheoryOfComputation/undecidable-problems/post-correspondence-problem/exists-not-tm2-decidable-pcp.md)

## Expansion

Both theorems are proved in Appendix B.2 of the source by a reduction of Post's correspondence problem: each instance is mapped to a formula of the respective fragment that is satisfiable iff the instance has a solution. The proof of Theorem 3.6 also uses Lemma B.1(ii) of the source, by which $\mathrm{PTL} \circ \mathrm{S4}_u$ formulas need only be considered in tt-models based on Aleksandrov topological spaces; a good expansion links that lemma. Decidability is regained when spatial variables are restricted to regions (regular closed sets) and the interaction between spatial and temporal constructors is limited, as in the decidable logics of the same paper.

## Sources

- D. Gabelaia, R. Kontchakov, A. Kurucz, F. Wolter and M. Zakharyaschev, "Combining spatial and temporal logics: expressiveness vs. complexity", *Journal of Artificial Intelligence Research* 23:167–243, 2005, <https://doi.org/10.1613/jair.1537>; read in the open-access author copy at <https://kuag19.github.io/homepage/gkkwz.pdf>: Section 3.2 (the fragments, Lemma B.1 as cited there, Theorems 3.6 and 3.7) and Appendix B.2.
