# Comparing polynomial interpretations is undecidable

Given a [polynomial interpretation](polynomial-interpretation.md) and two terms $s$ and $t$, it is undecidable whether $P_s > P_t$. If all the polynomials are linear, the question is decidable: $\sum_i k_i a_i + k > 0$ for all $a_1, \dots, a_n \ge 1$ if and only if $k_i \ge 0$ for all $i$ and $\sum_i k_i + k > 0$.

**Proof idea.** Undecidability by reduction from Hilbert's tenth problem, whether an integer polynomial has a root in the natural numbers, which is undecidable because every recursively enumerable set is Diophantine, by the [Davis–Putnam–Robinson–Matiyasevich theorem](../../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md), and some recursively enumerable set, such as [the halting set](../../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/exists-not-tm2-decidable-tm2-halts-on.md), is undecidable. The linear case: a negative $k_i$ makes the expression negative for large $a_i$, and otherwise the minimum is at $a_1 = \dots = a_n = 1$.

## Depends on

- [Polynomial interpretation](polynomial-interpretation.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)
- [Some multi-stack machine has an undecidable halting set](../../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/exists-not-tm2-decidable-tm2-halts-on.md)

## Sources

- U. Waldmann, *Automated Reasoning*, lecture notes, Max Planck Institute for Informatics, winter semester 2019/20, <https://rg1-teaching.mpi-inf.mpg.de/autrea-ws19/script.pdf>, Section 4.5, Theorem 4.23 (Hilbert's tenth problem is undecidable), Proposition 4.24 and the easy linear case, pp. 116–117.
