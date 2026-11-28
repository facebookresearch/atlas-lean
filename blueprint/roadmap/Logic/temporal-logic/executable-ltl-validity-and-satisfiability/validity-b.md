# Executable validity check for LTL

Let $\mathrm{Atom}$ be a finite type of atomic propositions with decidable equality. The executable validity check of an LTL formula $\varphi$ over $\mathrm{Atom}$ runs the [Boolean model checker](../model-checking-for-linear-temporal-logic/check-b.md) on the [universal valuation system](all-valuations.md), started from all valuations, with an atom $a$ true at a valuation $v$ exactly when $v(a) = \mathrm{true}$. By its [correctness](validity-b-iff.md), it returns $\mathrm{true}$ exactly when $\varphi$ holds on every ω-word of sets of atoms.
