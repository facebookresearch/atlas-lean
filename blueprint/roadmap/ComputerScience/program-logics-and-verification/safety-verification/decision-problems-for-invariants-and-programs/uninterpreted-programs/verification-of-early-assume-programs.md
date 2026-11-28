# Verification of uninterpreted programs with early assumes is undecidable

The verification problem stays undecidable for uninterpreted programs all of whose executions have early assumes, so the memoizing half of coherence cannot be dropped from the decidability theorem for coherent programs.

**Theorem.** The [verification problem](uninterpreted-programs-and-their-verification.md) restricted to uninterpreted programs all of whose executions have early assumes is undecidable: no algorithm decides, given such a program $s$ over variables $V$ and a postcondition $\varphi$ (a Boolean combination of equalities between variables), whether every complete execution of $s$ that is feasible in a data model satisfies $\varphi$ in that model.

## Depends on

- [Uninterpreted programs and their verification problem](uninterpreted-programs-and-their-verification.md)
- [Decidability by multi-stack machines](../../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Proof sketch

The proof is a reduction from the halting problem for two-counter machines. A fake counter $c^*$ advances in every simulated step and stays ahead of the real counters, and the equality assumptions (that $g$ inverts $f$, and auxiliary equalities used for zero tests) are made on $c^*$, except the single auxiliary equality $s_1(0) = s_2(0)$ on $0$ (Appendix B.1 of the source), so they are early; the real simulation makes only disequality assumptions. These executions are not memoizing. By contrast, the problem is decidable for coherent programs, which are both memoizing and have early assumes. The halting problem for two-counter machines started with both counters at $0$ is stated on the linked universality page.

## Sources

- Umang Mathur, P. Madhusudan and Mahesh Viswanathan, "Decidable verification of uninterpreted programs", *Proceedings of the ACM on Programming Languages* 3(POPL), 29 pages, 2019, <https://doi.org/10.1145/3290359>; read as arXiv:1811.00192v4, <https://arxiv.org/abs/1811.00192v4>: the corresponding theorem of Section 4 of that version, with the proof in the appendix on the undecidability of the verification problem.
