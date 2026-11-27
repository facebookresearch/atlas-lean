# Recognizing axiomatizations of superintuitionistic implicational calculi is undecidable

For every finitely axiomatized calculus containing the intuitionistic implicational calculus, over any signature containing implication, no algorithm decides whether a given finite set of axioms axiomatizes it, nor whether a given subcalculus of it is complete.

**Theorem (Bokov, 2015).** Fix a signature $\Sigma \supseteq \{\to\}$ and a [$\Sigma$-calculus](propositional-calculi-with-modus-ponens-and.md) $P_0$ with $P_0 \geq \mathbf{Int}_{\{\to\}}$. Then the problems of recognizing axiomatizations (Axm: given a $\Sigma$-calculus $P$, is $P \sim P_0$?) and of recognizing completeness (Cmpl: given $P \leq P_0$, is $P_0 \leq P$?) are undecidable (Theorem 2.7).

Here $P_0$ is fixed and $P$ ranges over finite sets of $\Sigma$-formulas, with modus ponens and substitution as rules. For instance, Axm and Cmpl are undecidable for $\mathbf{Int}_{\{\to\}}$ and $\mathbf{Cl}_{\{\to\}}$ themselves; for $\mathbf{Cl}_{\{\to\}}$, Axm is Markov's 1961 problem, first shown undecidable by Marcinkowski (1994).

## Depends on

- [Propositional calculi with modus ponens and substitution](propositional-calculi-with-modus-ponens-and.md)

## Proof depends on

- [Tag systems emulate Turing machines](../../../TheoryOfComputation/equivalence-of-models/tag-systems/tag-systems-emulate-turing-machines.md)

## Expansion

The proof reduces the halting problem for Post tag systems (Minsky: some tag system has an undecidable halting problem) to Cmpl. For a tag system $T$ and a word $\omega$ one effectively builds a calculus $P_{T,\omega,P_0} \leq P_0$ whose axioms code the productions of $T$, such that $P_0 \leq P_{T,\omega,P_0}$ iff $T$ halts on $\omega$. Cmpl is then undecidable, and since $P \leq P_0$ is guaranteed by the construction, so is Axm. Earlier, Zolin had proved the analogue for calculi containing $\mathbf{Int}_{\{\wedge,\to\}}$; the 2016 sequel by the same author weakens the hypothesis to $P_0 \geq \{x \to (y \to x)\}$.

## Sources

- Grigoriy V. Bokov, "Undecidability of the problem of recognizing axiomatizations for propositional calculi with implication", *Logic Journal of the IGPL* 23(2):341–353, 2015, doi:10.1093/jigpal/jzu047; read as arXiv:1407.7010v1, <https://arxiv.org/abs/1407.7010v1>: Theorem 2.7, Theorem 2.6, Theorem 3.1 (Minsky) and Section 3 of arXiv:1407.7010v1.
