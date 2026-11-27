# LTL with past-majority or most-frequent-letter operators is undecidable

Adding to the finally-only fragment of LTL on finite words either the past-majority operator or the most-frequent-letter operator makes both satisfiability and model checking over Kripke structures undecidable.

**Theorem (Bednarczyk and Michaliszyn).** For the logics of [LTL with percentage operators](ltl-with-percentage-operators.md), interpreted over finite words:

1. satisfiability of $\mathrm{LTL}_{\mathbf{F}}[\mathbf{H}]$ is undecidable (Theorem 4.5), and model checking of $\mathrm{LTL}_{\mathbf{F}}[\mathbf{H}]$ formulas over Kripke structures is undecidable (Theorem 4.6);
2. satisfiability and model checking of $\mathrm{LTL}_{\mathbf{F}}[\mathbf{M}]$ are undecidable (Corollary 4.7);
3. satisfiability and model checking of $\mathrm{LTL}_{\mathbf{F}}[\mathbf{MF}]$ are undecidable (Theorem 4.17).

The formula, and for model checking the Kripke structure, are the input; the set of atomic propositions is not fixed. Restricting how percentage operators combine with negation and $\mathbf{G}$ restores decidability (Section 5).

## Depends on

- [LTL with percentage operators](ltl-with-percentage-operators.md)
- [Kripke model](../../modal-logic/kripke-semantics/kripke-model.md)

## Proof depends on

- [Two-counter machines are universal](../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The reduction is from reachability of a given state by a Minsky (two-counter) machine. A word is *shadowy* if its length is even, its even positions carry a letter $\mathit{white}$ and its odd positions a letter $\mathit{shadow}$; shadowy words are definable with $\mathbf{H}$. For a machine $M$ and a state $q$, an $\mathrm{LTL}_{\mathbf{F}}[\mathbf{H}]$ formula describes shadowy words whose white positions spell, letter by letter, the transitions of a run of $M$ (source and target states, whether each counter is zero, and the operation on each counter), with counter values kept consistent by comparing counts through $\mathbf{H}$; it has a model iff $M$ reaches $q$. Model checking reduces from satisfiability via the Kripke structure whose traces are all words over $2^{\mathrm{AP}}$. Since $\mathbf{H}\varphi \equiv \mathbf{M}\varphi \wedge \mathbf{M}\neg\varphi$, clause 2 follows; $\mathbf{H}$ is not definable from $\mathbf{MF}$, but $\mathbf{MF}$ simulates enough of it for the same reduction (Sections 4.3 and 4.4). Decidability is regained in the logic $\mathrm{LTL}^{\%}$, which allows arbitrary LTL together with percentage constraints $\mathbf{P}_{\bowtie k\%}\psi$ on LTL formulas $\psi$ as long as they are not mixed with $\mathbf{G}$ (Section 5).

## Sources

- Bartosz Bednarczyk and Jakub Michaliszyn, "“Most of” leads to undecidability: Failure of adding frequencies to LTL", in *Foundations of Software Science and Computation Structures (FoSSaCS 2021)*, Lecture Notes in Computer Science 12650, Springer, 2021, pp. 82–101, doi:10.1007/978-3-030-71995-1_5; read as arXiv:2007.01233v4, <https://arxiv.org/abs/2007.01233v4>: Theorems 4.5, 4.6 and 4.17, Corollary 4.7, Sections 4 and 5 of arXiv:2007.01233v4.
