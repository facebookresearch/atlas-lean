# Completeness of SLD resolution

Let $P$ be a definite logic program and $Q$ a query, in the setting of [SLD resolution](sld-resolution.md). A substitution $\theta$ is a *correct answer substitution* of $Q$ if $P \models Q\theta$.

1. **Strong completeness.** If $\theta$ is a correct answer substitution of $Q$, then for every selection rule $R$ there is a successful SLD derivation of $P \cup \{Q\}$ via $R$ whose computed answer substitution $\eta$ is at least as general as $\theta$.
2. **Ground atoms.** Over a signature with at least one constant symbol, if $A$ is a ground atom in the [least Herbrand model](least-herbrand-model-of-a-definite-logic-program.md) $M_P$, then for every selection rule the query $A$ has a successful SLD derivation via that rule, an SLD refutation of $\leftarrow A$.

## Proof sketch

The proof of part 1 interprets $P$ in the term model built from implication trees. A correct answer makes every atom of $Q\theta$ the root of an implication tree. An induction on the total number of nodes of these trees then constructs the derivation for an arbitrary selection rule.

Part 2 follows from part 1. Every atom of $M_P$ is a logical consequence of $P$, by part 1 of [Ground logical consequences of a definite program](ground-logical-consequences-of-a-definite-program.md), so the empty substitution is a correct answer substitution of $A$.

## Depends on

- [SLD resolution](sld-resolution.md)
- [Least Herbrand model of a definite logic program](least-herbrand-model-of-a-definite-logic-program.md)

## Proof depends on

- [Ground logical consequences of a definite program](ground-logical-consequences-of-a-definite-program.md)

## Sources

- H. Strass (based on slides by M. Thielscher), *Correctness of SLD Resolution*, Lecture 4 of Foundations of Logic Programming, TU Dresden, 2026, <https://iccl.inf.tu-dresden.de/w/images/3/33/FLP2026-04.pdf>: correct and computed answer substitutions, implication trees, term interpretations and the term model $C(P)$ (Lemmas 4.7 and 4.12), Lemma 4.15 ($n$-deep queries), Theorem 4.13 (completeness for every selection rule), and Herbrand interpretations over the Herbrand universe (slide 21), where an algebra's domain is a nonempty set (slide 5).
- H. Strass (based on slides by M. Thielscher), *Least Herbrand Models*, Lecture 5 of Foundations of Logic Programming, TU Dresden, 2026, <https://iccl.inf.tu-dresden.de/w/images/8/8b/FLP2026-05.pdf>: Theorem 4.37, (i) implies (iii) (for a ground atom $A$, if $M(P) \Vdash A$, then every SLD tree for $P \cup \{A\}$ is successful), and Theorem 4.29 ($M(P)$ is the least Herbrand model of $P$).
- J. W. Lloyd, *Foundations of Logic Programming*, 2nd ed., Springer, 1987.
