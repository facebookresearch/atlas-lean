# Complete rewriting is NP-complete even without repeated relation names

Deciding whether a conjunctive query $Q$ has a complete rewriting using a set $\mathcal V$ of conjunctive views,
neither with built-in comparison atoms, is NP-complete even when no relation name repeats in the body of $Q$ or of any
view, so that every rule is nonredundant and at most one containment mapping goes from each view to $Q$. Hardness is
by reduction from exact cover by 3-sets.

## Depends on

- [Rewritings of conjunctive queries using views](rewritings-of-conjunctive-queries-using-views.md)
- [NP-complete decision problems](../../../TheoryOfComputation/complexity-classes/mahaney-s-theorem/npcomplete.md)

## Proof depends on

- [Finding small and complete rewritings of conjunctive queries is NP-complete](finding-small-and-complete-rewritings-is-np-complete.md)
- [EXACT COVER BY 3-SETS is NP-complete](../../../TheoryOfComputation/np-completeness/set-systems-and-location/exact-cover-by-3-sets/exact-cover-by3-sets-np-complete.md)

## Sources

- A. Y. Levy, A. O. Mendelzon, Y. Sagiv and D. Srivastava, "Answering queries using views", *Proceedings of the 14th ACM Symposium on Principles of Database Systems (PODS)*, 1995, pp. 95–104, Theorem 3.10 with its proof (p. 100).
