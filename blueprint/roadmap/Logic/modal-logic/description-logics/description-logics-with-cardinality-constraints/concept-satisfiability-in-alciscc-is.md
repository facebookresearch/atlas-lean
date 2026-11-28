# Concept satisfiability in ALCISCC++ is undecidable

Adding inverse roles to the description logic $\mathcal{ALCSCC}^{++}$, whose Presburger constraints mix global and local cardinalities, makes concept satisfiability over finite interpretations undecidable, while without inverses it is NEXPTIME-complete.

**Theorem (Baader, Bednarczyk and Rudolph).** Satisfiability of [$\mathcal{ALCISCC}^{++}$](alcscc-with-global-and-local-cardinality.md) concept descriptions, that is, whether a given concept has a nonempty extension in some finite interpretation, is undecidable (Theorem 23).

Without inverse roles, satisfiability of $\mathcal{ALCSCC}^{++}$ concepts is NEXPTIME-complete (Theorem 8).

## Depends on

- [The description logic ALCSCC++ with global and local cardinality constraints](alcscc-with-global-and-local-cardinality.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

Inverse roles allow multiplication of concept cardinalities: with auxiliary roles $r$ and $s$, the constraints $A \equiv \exists r.\top$, $B \equiv \exists r^-.\top$, $A \sqsubseteq \mathrm{sat}(B = r)$, $B \sqsubseteq \mathrm{sat}(A = r^-)$ make $r$ connect every element of $A$ with every element of $B$; then $\top \sqsubseteq \mathrm{sat}(|r| = |s|)$, $C \equiv \exists s^-.\top$ and $\top \sqsubseteq \mathrm{sat}(|s^-| \leq 1)$ force $|C| = |A| \cdot |B|$. Addition is already expressible by global cardinality constraints, so a Diophantine equation has a solution in the naturals iff a corresponding concept is satisfiable, and Hilbert's tenth problem reduces to concept satisfiability.

## Sources

- Franz Baader, Bartosz Bednarczyk and Sebastian Rudolph, "Satisfiability and query answering in description logics with global and local cardinality constraints", in *ECAI 2020: 24th European Conference on Artificial Intelligence*, Frontiers in Artificial Intelligence and Applications 325, IOS Press, 2020, doi:10.3233/FAIA200146; read as arXiv:2002.06072v1, <https://arxiv.org/abs/2002.06072v1>: Theorem 23 with the example preceding it in Section 5, and Theorem 8, of arXiv:2002.06072v1.
