# Completeness of propositional tableaux

A finite set $\{F_1, \dots, F_n\}$ of propositional formulas is satisfiable if and only if there is no closed strict [tableau](propositional-semantic-tableau.md) for it. Consequently a propositional formula $F$ is valid if and only if a strict maximal tableau for $\{\neg F\}$ is closed, whichever strict maximal tableau is constructed.

**Proof.** A closed tableau refutes the set by soundness. Conversely, if no strict tableau is closed, a strict maximal tableau, which exists and is finite, has an open path; that path is maximal, so its formulas, among them $F_1, \dots, F_n$, are satisfiable.

## Depends on

- [Propositional semantic tableau](propositional-semantic-tableau.md)

## Proof depends on

- [Soundness of propositional tableaux](soundness-of-propositional-tableaux.md)
- [Strict propositional tableau expansions are finite](strict-tableau-expansions-are-finite.md)
- [Maximal open tableau paths are satisfiable](maximal-open-paths-are-satisfiable.md)
- [Tableau expansion preserves satisfiability](tableau-expansion-preserves-satisfiability.md)

## Sources

- U. Waldmann, *Automated Reasoning*, lecture notes, Max Planck Institute for Informatics, winter semester 2019/20, <https://rg1-teaching.mpi-inf.mpg.de/autrea-ws19/script.pdf>, Section 3.18, Theorem 3.56 with its proof and the consequences listed after it, pp. 98–99.
