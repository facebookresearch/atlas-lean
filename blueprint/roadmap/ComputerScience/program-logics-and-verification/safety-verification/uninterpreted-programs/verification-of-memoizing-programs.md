# Verification of memoizing uninterpreted programs is undecidable

The verification problem stays undecidable for uninterpreted programs all of whose executions are memoizing, so the early-assumes half of coherence cannot be dropped from the decidability theorem for coherent programs.

**Theorem.** The [verification problem](uninterpreted-programs-and-their-verification.md) restricted to uninterpreted programs all of whose executions are memoizing is undecidable: no algorithm decides, given such a program $s$ over variables $V$ and a postcondition $\varphi$ (a Boolean combination of equalities between variables), whether every complete execution of $s$ that is feasible in a data model satisfies $\varphi$ in that model.

## Depends on

- [Uninterpreted programs and their verification problem](uninterpreted-programs-and-their-verification.md)

## Proof depends on

- [Two-counter machines are universal](../../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The proof is again a reduction from the halting problem for two-counter machines. The counters are simulated on terms built from a variable $x$ standing for $0$ without any equality assumption, so they live in a free model, while a fake counter on a second copy $y$ of $0$ forces $g$ to invert $f$ and auxiliary functions to behave as needed for zero tests. When the machine halts, a single assumption $x = y$ merges the two models and makes the simulation correct. Executions are memoizing, and already one assumption that is not early suffices for undecidability. By contrast, the problem is decidable for coherent programs, which are both memoizing and have early assumes.

## Sources

- Umang Mathur, P. Madhusudan and Mahesh Viswanathan, "Decidable verification of uninterpreted programs", *Proceedings of the ACM on Programming Languages* 3(POPL), 29 pages, 2019, <https://doi.org/10.1145/3290359>; read as arXiv:1811.00192v4, <https://arxiv.org/abs/1811.00192v4>: the corresponding theorem of Section 4 of that version, with the proof in the appendix on the undecidability of the verification problem.
