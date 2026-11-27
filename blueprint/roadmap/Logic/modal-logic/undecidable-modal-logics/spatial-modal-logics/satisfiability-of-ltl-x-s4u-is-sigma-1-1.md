# Satisfiability of LTL × S4u is Σ¹₁-complete

Satisfiability of the spatio-temporal logic combining linear temporal logic over the natural numbers with the topological logic S4u is Σ¹₁-complete, and already its fragment with only "always" and "eventually" is undecidable over finite flows of time and under the finite state assumption.

**Theorem (Gabelaia, Kontchakov, Kurucz, Wolter and Zakharyaschev).** For the logics of the page on [topological temporal models](spatio-temporal-logic-ptl-x-s4u.md):

1. the satisfiability problem for $\mathrm{LTL} \times \mathrm{S4}_u$ formulas in tt-models (over the flow of time $(\mathbb N, <)$) is $\Sigma^1_1$-complete (Theorem 1.20 of the survey);
2. the satisfiability problem for $\mathrm{LTL}_\Box \times \mathrm{S4}_u$ formulas in arbitrary finite tt-models is undecidable, and so is the satisfiability problem for $\mathrm{LTL}_\Box \times \mathrm{S4}_u$ formulas in tt-models satisfying the finite state assumption (Theorem 1.21).

For the full language with past operators, the journal paper states that satisfiability of $\mathrm{PTL} \times \mathrm{S4}_u$ formulas in tt-models based on $(\mathbb N, <)$ or $(\mathbb Z, <)$ is undecidable (its Theorem 3.3), and remains undecidable over arbitrary finite flows of time and, over $(\mathbb N, <)$ or $(\mathbb Z, <)$, under the finite state assumption (its Theorem 3.5). Both components of the combination are PSPACE-complete on their own.

## Depends on

- [Topological temporal models and the spatio-temporal logic PTL × S4u](spatio-temporal-logic-ptl-x-s4u.md)

## Proof depends on

None.

## Expansion

The $\Sigma^1_1$ lower bound is proved by a reduction of the $\Sigma^1_1$-complete recurrent tiling problem; the terms used in the proof may denote arbitrary, not necessarily connected, sets. A good expansion links the $\Sigma^1_1$-completeness of the recurrent tiling problem, which has no page yet, and the upper bound, which places satisfiability in $\Sigma^1_1$. Restricting terms to regular closed sets (regions) is what yields decidable spatio-temporal logics in the same papers.

## Sources

- D. Gabelaia, R. Kontchakov, A. Kurucz, F. Wolter and M. Zakharyaschev, "Combining spatial and temporal logics: expressiveness vs. complexity", *Journal of Artificial Intelligence Research* 23:167–243, 2005, <https://doi.org/10.1613/jair.1537>; read in the open-access author copy at <https://kuag19.github.io/homepage/gkkwz.pdf>: Section 3.2, Theorems 3.3 and 3.5.
- R. Kontchakov, A. Kurucz, F. Wolter and M. Zakharyaschev, "Spatial logic + temporal logic = ?", in *Handbook of Spatial Logics*, Springer, 2007, pp. 497–564, <https://doi.org/10.1007/978-1-4020-5587-4_9>; read in the open-access author copy at <https://kuag19.github.io/homepage/st.pdf>: Section 4, Theorems 1.20 and 1.21 and the remarks after Theorem 1.20 on the recurrent tiling reduction.
