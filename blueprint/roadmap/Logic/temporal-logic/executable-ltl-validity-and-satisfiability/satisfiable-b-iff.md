# Correctness of the executable LTL satisfiability check

Let $\mathrm{Atom}$ be a finite type of atomic propositions with decidable equality. For every LTL formula $\varphi$ over $\mathrm{Atom}$, the [executable satisfiability check](satisfiable-b.md) returns $\mathrm{true}$ if and only if some ω-word $W$ of sets of atoms [satisfies](../linear-temporal-logic/satisfies.md) $\varphi$, an atom $a$ holding at a set $s$ when $a \in s$.
