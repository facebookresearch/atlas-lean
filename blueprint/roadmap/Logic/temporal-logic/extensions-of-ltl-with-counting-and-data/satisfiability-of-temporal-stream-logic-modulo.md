# Satisfiability of temporal stream logic modulo theories is highly undecidable

Satisfiability of temporal stream logic formulas modulo the theory of uninterpreted functions, the theory of equality, or Presburger arithmetic is neither semi-decidable nor co-semi-decidable, and the same holds for validity.

**Theorem (Finkbeiner, Heim and Passing).** For each of the theories $T_U$ (uninterpreted functions), $T_E$ (equality) and $T_N$ (Presburger arithmetic), the problem of deciding whether a given formula of [temporal stream logic](temporal-stream-logic-modulo-theories.md) is satisfiable in the theory is neither semi-decidable nor co-semi-decidable (Theorems 4, 5 and 6 for $T_U$, $T_N$ and $T_E$); by duality (Theorem 1) the same holds for validity in the theory.

Here the formula is the input, and the cells and symbols are those occurring in it. Restricted fragments are better behaved: in $T_U$, satisfiability is decidable for formulas with only next operators and at most one top-level eventually operator, and semi-decidable for the reachability fragment and for formulas with a single cell (Section 6).

## Depends on

- [Temporal stream logic modulo theories](temporal-stream-logic-modulo-theories.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Totality is not recognizable](../../../TheoryOfComputation/computability/totality-problem-for-programs/not-tm2-recognizable-total.md)
- [Totality is not co-recognizable](../../../TheoryOfComputation/computability/totality-problem-for-programs/not-tm2-co-recognizable-total.md)

## Expansion

In $T_U$ a TSL formula $\varphi_{\mathit{num}}$ forces a constant $z$, a unary function $f$ and a binary predicate $\approx$ to behave as zero, successor and equality: $f^a(z) \approx f^b(z)$ holds iff $a = b$. Using this encoding, every GOTO program $\mathcal{G}$ yields a formula $\varphi_{\mathcal{G}}$ that simulates $\mathcal{G}$ on inputs $0, 1, 2, \dots$, moving to the next input whenever the halting location is reached and requiring that this happens infinitely often; $\varphi_{\mathcal{G}} \wedge \varphi_{\mathit{num}}$ is satisfiable in $T_U$ iff $\mathcal{G}$ terminates on every input. The universal halting problem for GOTO programs, like that for Turing machines, is neither semi-decidable nor co-semi-decidable. Presburger arithmetic provides zero, successor and equality directly, and in $T_E$ a further formula enforces a function and a constant to behave as successor and zero. The full version (arXiv:2104.14988v2, Appendix C) states the general form: satisfiability is neither semi-decidable nor co-semi-decidable in every theory $T$ in which some TSL formula encodes resetting a cell to zero, incrementation and equality.

## Sources

- Bernd Finkbeiner, Philippe Heim and Noemi Passing, "Temporal stream logic modulo theories", in *Foundations of Software Science and Computation Structures (FoSSaCS 2022)*, Lecture Notes in Computer Science 13242, Springer, 2022, pp. 325–346, doi:10.1007/978-3-030-99253-8_17; read as arXiv:2104.14988v2, <https://arxiv.org/abs/2104.14988v2>: Section 5 (the theorems "Undecidability of TSL-$T_U$-SAT", "Undecidability of TSL-$T_N$-SAT" and "Undecidability of TSL-$T_E$-SAT" and the encoding lemma for numbers), Appendix C (the theorem on high undecidability of TSL satisfiability in theories encoding reset, increment and equality, and the universal halting problem for GOTO programs) and Section 6 of arXiv:2104.14988v2.
