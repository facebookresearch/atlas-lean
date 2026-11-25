# Termination by disjunctively well-founded transition invariants

Let $R$ be a transition relation and $\mathit{Reach}$ the set of states reachable from the initial states. A *transition invariant* is a relation $T$ with $R^+ \cap (\mathit{Reach} \times \mathit{Reach}) \subseteq T$. A relation is *disjunctively well-founded* if it is a finite union of well-founded relations. The program terminates from every initial state (there is no infinite $R$-path from a reachable state) if and only if it has a disjunctively well-founded transition invariant. The proof that a disjunctively well-founded transition invariant implies termination uses the infinite Ramsey theorem.

## Expansion

This page becomes ready once these prerequisites are stated:

- Disjunctive well-foundedness via Ramsey (proof prerequisite)

## Sources

- A. Podelski and A. Rybalchenko, "Transition invariants", *Proceedings of the 19th IEEE LICS*, 2004
- D. Kroening, N. Sharygina, A. Tsitovich and C. M. Wintersteiger, "Termination analysis with compositional transition invariants", *CAV 2010*, LNCS 6174, Springer, 2010, Section 2, Definitions 2 and 3 and Theorem 1 (restating Podelski and Rybalchenko), <https://ora.ox.ac.uk/objects/uuid:8b2f349e-62ee-4785-ad4f-56171d542797>
