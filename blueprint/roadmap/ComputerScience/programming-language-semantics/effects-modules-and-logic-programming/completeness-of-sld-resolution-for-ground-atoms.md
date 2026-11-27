# Completeness of SLD resolution

Let $P$ be a definite logic program and $Q$ a query, in the setting of [SLD resolution](sld-resolution.md). A substitution $\theta$ is a *correct answer substitution* of $Q$ if $P \models Q\theta$.

1. **Strong completeness.** If $\theta$ is a correct answer substitution of $Q$, then for every selection rule $R$ there is a successful SLD derivation of $P \cup \{Q\}$ via $R$ whose computed answer substitution $\eta$ is at least as general as $\theta$.
2. **Ground atoms.** If $A$ is a ground atom in the [least Herbrand model](least-herbrand-model-of-a-definite-logic-program.md) $M_P$, then for every selection rule the query $A$ has a successful SLD derivation via that rule, an SLD refutation of $\leftarrow A$.

Part 2 follows from part 1. Every atom of $M_P$ is a logical consequence of $P$, so the empty substitution is a correct answer substitution of $A$.

The proof of part 1 interprets $P$ in the term model built from implication trees. A correct answer makes every atom of $Q\theta$ the root of an implication tree. An induction on the total number of nodes of these trees then constructs the derivation for an arbitrary selection rule.

## Depends on

- [SLD resolution](sld-resolution.md)
- [Least Herbrand model of a definite logic program](least-herbrand-model-of-a-definite-logic-program.md)

## Proof depends on

- [Ground logical consequences of a definite program](ground-logical-consequences-of-a-definite-program.md)

## Sources

- H. Strass (based on slides by M. Thielscher), *Correctness of SLD Resolution*, Lecture 4 of Foundations of Logic Programming, TU Dresden, 2026, <https://iccl.inf.tu-dresden.de/w/images/3/33/FLP2026-04.pdf>: correct and computed answer substitutions, implication trees and Lemmas 4.26 and 4.28, Lemma 4.15 ($n$-deep queries), and Theorem 4.13 (completeness for every selection rule).
- J. W. Lloyd, *Foundations of Logic Programming*, 2nd ed., Springer, 1987.
