# Termination of term rewriting is undecidable

Consider finite [term rewriting systems](../automated-deduction/term-rewriting-systems.md) over finite signatures. Both of the following problems are undecidable:

1. given a finite term rewriting system $R$ and a term $t$, whether every $\to_R$-reduction starting from $t$ is finite;
2. given a finite term rewriting system $R$, whether $\to_R$ is terminating.

**Proof idea.** Encode Turing machines as rewrite rules, so that the computation of a machine corresponds to a reduction sequence, and reduce the halting problem for Turing machines to problem 1 and the uniform halting problem, whether a machine halts on every input, a form of the totality problem, to problem 2.

## Depends on

- [Term rewriting systems](../automated-deduction/term-rewriting-systems.md)
- [Abstract reduction system](abstract-reduction-system.md)

## Proof depends on

- [Halting is undecidable](../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)
- [Totality is undecidable](../../../TheoryOfComputation/computability/totality-problem-for-programs/not-tm2-decidable-total.md)

## Sources

- U. Waldmann, *Automated Reasoning*, lecture notes, Max Planck Institute for Informatics, winter semester 2019/20, <https://rg1-teaching.mpi-inf.mpg.de/autrea-ws19/script.pdf>, Section 4.5, Proposition 4.17 and its proof sketch, p. 114.
