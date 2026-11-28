# Satisfiability of counting CTL with diagonal constraints is undecidable

Whether some Kripke structure satisfies a counting CTL formula is undecidable once constraints may compare two counts with coefficients ±1, even without Boolean combinations in constraints.

**Theorem (Laroussinie, Meyer and Petonnet).** The [satisfiability problem](counting-ctl.md) for CCTL$_{\pm 1}$ is undecidable: there is no algorithm that decides, given a CCTL$_{\pm 1}$ formula $\Phi$, whose constraints are single linear constraints with coefficients in $\{-1, 1\}$, whether some finite Kripke structure has a state satisfying $\Phi$ (Theorem 5.1 of the source, by a reduction from the halting problem for two-counter machines).

Without diagonal constraints, satisfiability is 2EXPTIME-complete for every logic from CCTL$_1$ to CCTL$_\wedge$ (Theorem 5.2), and the same picture holds for the cumulative-semantics variants (Theorem 6.24: 2EXPTIME-complete from CCTL$^c_1$ to CCTL$^c_\wedge$, undecidable for CCTL$^c_{\pm 1}$).

## Depends on

- [Counting CTL](counting-ctl.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

As in the model-checking proof, for a two-counter machine $M$ one builds a CCTL$_{\pm 1}$ formula $\Phi_M$ over propositions $q_1, \ldots, q_n$ for the instructions and propositions for the operations $C^{+}, C^{-}, C_0, D^{+}, D^{-}, D_0$ and $\mathit{halt}$. $\Phi_M$ describes a linear Kripke structure in which every state carries exactly one instruction proposition and one operation proposition, consecutive states follow the instructions of $M$, the value of each counter at a position is the difference of the numbers of its increment and decrement states so far, zero tests are checked by diagonal constraints, and a $\mathit{halt}$ state is reached. $\Phi_M$ is satisfiable iff $M$ halts.

## Sources

- F. Laroussinie, A. Meyer and E. Petonnet, "Counting CTL", *Logical Methods in Computer Science* 9(1), 2013, paper 3, <https://doi.org/10.2168/LMCS-9(1:3)2013>; numbers from arXiv:1211.4651v4, <https://arxiv.org/abs/1211.4651v4>: Theorem 5.1 and its proof, Theorem 5.2 and Theorem 6.24.
