# Verification of uninterpreted programs is undecidable

No algorithm decides, given a while program over uninterpreted functions and an equality postcondition, whether every execution feasible in some data model satisfies the postcondition; recursion is not needed.

**Theorem.** The [verification problem](uninterpreted-programs-and-their-verification.md) restricted to uninterpreted programs (without procedure calls) is undecidable: no algorithm decides, given such a program $s$ over variables $V$ and a postcondition $\varphi$ (a Boolean combination of equalities between variables), whether every complete execution of $s$ that is feasible in a data model satisfies $\varphi$ in that model.

## Depends on

- [Uninterpreted programs and their verification problem](uninterpreted-programs-and-their-verification.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Proof sketch

The proof reduces the halting problem for two-counter machines. A configuration is held in a variable $x_{\mathrm{curr}}$ for the control state, compared with constants $x_q$ ($q \in Q$), and variables $y_1, y_2$ for the counters; a counter value $i$ is represented by the term $f^i(0)$, and the program forces the data model to provide two unary functions $f$ and $g$ (increment and decrement) that are mutually inverse on the terms representing counter values. A complete execution feasible in some data model then exists iff the machine halts. Two unary function symbols suffice. The programs built this way are neither memoizing nor have early assumes, and no bounded number of ghost variables makes them coherent. By contrast, the problem is decidable for coherent programs, which are both memoizing and have early assumes. The halting problem for two-counter machines started with both counters at $0$ is stated on the linked universality page.

## Sources

- Umang Mathur, P. Madhusudan and Mahesh Viswanathan, "Decidable verification of uninterpreted programs", *Proceedings of the ACM on Programming Languages* 3(POPL), 29 pages, 2019, <https://doi.org/10.1145/3290359>; read as arXiv:1811.00192v4, <https://arxiv.org/abs/1811.00192v4>: the corresponding theorem of Section 4 of that version, with the proof in the appendix on the undecidability of the verification problem.
