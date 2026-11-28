# Recognizing extensions of a propositional calculus is undecidable

For every fixed propositional calculus with implication, no algorithm decides whether a given calculus derives all of its theorems; if the fixed calculus derives $x \to (y \to x)$, recognizing its axiomatizations and the completeness of its subcalculi is undecidable as well.

**Theorem (Bokov, 2016).** Fix a signature $\Sigma \supseteq \{\to\}$ and a [$\Sigma$-calculus](propositional-calculi-with-modus-ponens-and.md) $P_0$ with at least one axiom. Then (Theorem 2.10):

1. recognizing extensions (Ext: given a $\Sigma$-calculus $P$, is $P_0 \leq P$?) is undecidable;
2. recognizing completeness (Cmpl: given $P$ with $P \leq P_0$, is $P_0 \leq P$?) is undecidable if $P_0 \geq \{x \to (y \to x)\}$.

The source states clause 1 for every fixed calculus; for the calculus with no axioms every $P$ is an extension, so Ext is trivially decidable there, and the construction in the proof needs an axiom of $P_0$. Consequently, recognizing axiomatizations (Axm: given $P$, is $P \sim P_0$?) is undecidable whenever $P_0 \geq \{x \to (y \to x)\}$ (Corollary 2.11), and for every fixed $\Sigma$-formula $A$ the derivability problem "given a $\Sigma$-calculus $P$, does $P \vdash A$?" is undecidable (Corollary 2.12, the case $P_0 = \{A\}$ of clause 1), even when $A$ has the form $B \to B$.

## Depends on

- [Propositional calculi with modus ponens and substitution](propositional-calculi-with-modus-ponens-and.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Tag systems emulate Turing machines](../../../TheoryOfComputation/equivalence-of-models/tag-systems/tag-systems-emulate-turing-machines.md)

## Expansion

As in the 2015 paper, the proof simulates Post tag systems: for a tag system $T$ with undecidable halting problem (Minsky) and a word $\xi$ one builds a calculus $P_{T,P_0,\xi}$ such that $P_0 \leq P_{T,P_0,\xi}$ iff $T$ halts on $\xi$, which gives clause 1 with no assumption on $P_0$. If $\{x \to (y \to x)\} \leq P_0$, then $P_{T,P_0,\xi} \leq P_0$, so the same instances witness clause 2. Clause 2 strengthens the earlier result for $P_0 \geq \mathbf{Int}_{\{\to\}}$, and clause 1 strengthens Marcinkowski's theorem for one-axiom calculi. The source also states, with proof left to the reader, that Axm and Cmpl remain undecidable for $P_0 \geq \{x \to (F \to x)\}$ whenever $F$ does not contain $x$ (Theorem 5.1).

## Sources

- Grigoriy V. Bokov, "Undecidable problems for propositional calculi with implication", *Logic Journal of the IGPL* 24(5):792–806, 2016, doi:10.1093/jigpal/jzw013; read as arXiv:1502.00978v1, <https://arxiv.org/abs/1502.00978v1>: Theorem 2.10, Corollaries 2.11 and 2.12, Theorems 2.4, 2.7, 3.2 and 5.1, and Section 4 of arXiv:1502.00978v1.
