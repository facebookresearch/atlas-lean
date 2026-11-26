# Compactness theorem for first-order logic

Let $L$ be a first-order language and $T$ a theory, a set of $L$-sentences. Then $T$ is satisfiable, that is, it has a model, if and only if it is finitely satisfiable: every finite subset of $T$ has a model. For countable sets of formulas the theorem is due to K. Gödel (1930). Waldmann derives it from the refutational completeness of resolution: a set of closed formulas is transformed by Skolemization and clausal normal form into an equisatisfiable clause set, and a resolution refutation uses only finitely many of its clauses.

## Sources

- U. Waldmann, *Automated Reasoning*, lecture notes, Max Planck Institute for Informatics, winter semester 2019/20, <https://rg1-teaching.mpi-inf.mpg.de/autrea-ws19/script.pdf>, Section 3.12, Theorem 3.39 (compactness theorem for first-order logic) and its proof, p. 80.
- Mathlib, `FirstOrder.Language.Theory.isSatisfiable_iff_isFinitelySatisfiable` in `Mathlib/ModelTheory/Satisfiability.lean`.
