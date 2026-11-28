# Satisfiability of time-prefixed hypertrace formulas is undecidable

Already for time-prefixed hypertrace formulas with the quantifier prefix ∃∀∃²∀ over time followed by one universal and two existential constrained and one existential unconstrained trace quantifier, no algorithm decides whether some set of traces satisfies the formula.

**Theorem (Chalupa, Henzinger and Oliveira da Costa).** Let $Q$ be the quantifier prefix

$$
\exists i_1\, \forall i_2\, \exists i_3\, \exists i_4\, \forall i_5\; \forall \pi_1 \mathbin{::} T\; \exists \pi_2 \mathbin{::} T\; \exists \pi_3 \mathbin{::} T\; \exists \pi_4 ,
$$

with five time quantifiers followed by four trace quantifiers, of which the first three are constrained. It is undecidable, given a quantifier-free formula $\varphi'$, whether the [hypertrace formula](hypertrace-logic.md) $\varphi = Q\, \varphi'$ is satisfiable, that is, whether $[\![\varphi]\!] \ne \varnothing$ (Theorem 22 of the source, Section 6).

The source also shows that trace-prefixed formulas with prefix $\forall \pi_1 \mathbin{::} T\, \forall \pi_2 \mathbin{::} T\, \exists \pi'_1 \mathbin{::} T$ followed by time quantifiers have undecidable satisfiability (Proposition 15), that formulas without constrained trace quantifiers are equivalent to S1S and hence decidable (Theorem 7 and Corollary 8), and that formulas whose only alternation between constrained trace quantifiers is from existential to universal are decidable (Theorem 12 and Corollary 16).

## Depends on

- [Hypertrace logic with constrained and unconstrained trace quantifiers](hypertrace-logic.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)
- [Halting is undecidable](../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

The proof reduces the non-halting problem for two-counter Minsky machines. Each trace of a model encodes one configuration, with the counters in unary as the number of positions where $\mathit{mem}_1$ or $\mathit{mem}_2$ holds, together with the transition taken next; the unconstrained trace quantifier guesses the time point where an increment or decrement happens, and the constrained quantifiers require every configuration in the model to have its successor configuration in the model.

## Sources

- Marek Chalupa, Thomas A. Henzinger and Ana Oliveira da Costa, "Flavors of quantifiers in hyperlogics", in *45th IARCS Annual Conference on Foundations of Software Technology and Theoretical Computer Science (FSTTCS 2025)*, LIPIcs 360, 20:1–20:18, 2025, doi:[10.4230/LIPIcs.FSTTCS.2025.20](https://doi.org/10.4230/LIPIcs.FSTTCS.2025.20). Numbering of the version read, arXiv:2510.12298v1: Theorem 7, Corollary 8, Theorem 12, Proposition 15, Corollary 16 and Theorem 22 (Sections 4 to 6), with the full proofs in the appendix.
