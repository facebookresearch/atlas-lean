# Tableau expansion preserves satisfiability

Let $T$ be a [tableau](propositional-semantic-tableau.md) for a finite set $\{F_1, \dots, F_n\}$ of propositional formulas. Then $\{F_1, \dots, F_n\}$ is satisfiable if and only if the set of formulas on some path of $T$ is satisfiable.

**Proof.** Every path contains $F_1, \dots, F_n$, which gives one direction. The other follows by induction on the construction of $T$: a valuation satisfying the formulas on a path also satisfies the formulas added on at least one of the extended paths.

## Depends on

- [Propositional semantic tableau](propositional-semantic-tableau.md)

## Sources

- U. Waldmann, *Automated Reasoning*, lecture notes, Max Planck Institute for Informatics, winter semester 2019/20, <https://rg1-teaching.mpi-inf.mpg.de/autrea-ws19/script.pdf>, Section 3.18, Theorem 3.51 with its proof, p. 97.
