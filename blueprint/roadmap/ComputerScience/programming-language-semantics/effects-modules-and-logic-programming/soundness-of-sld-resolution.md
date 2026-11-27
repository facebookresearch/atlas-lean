# Soundness of SLD resolution

If a definite program $P$ has an SLD refutation of the goal $\leftarrow Q$ with computed answer $\theta$, then $Q\theta$ is a logical consequence of $P$: the universal closure of $Q\theta$ is true in every model of $P$. In particular, over a signature with at least one constant symbol, every ground atom with an SLD refutation belongs to the least Herbrand model $M_P$.

## Depends on

- [SLD resolution](sld-resolution.md)
- [Least Herbrand model of a definite logic program](least-herbrand-model-of-a-definite-logic-program.md)
- [Unification of ranked terms through the curried encoding](../../../Logic/first-order-logic/first-order-unification/unification-of-ranked-terms-through-the-curried-encoding.md)

## Proof depends on

- [Ground logical consequences of a definite program](ground-logical-consequences-of-a-definite-program.md)

## Sources

- J. W. Lloyd, *Foundations of Logic Programming*, 2nd ed., Springer, 1987
- K. R. Apt, *From Logic Programming to Prolog*, Prentice Hall, 1997
- H. Strass (based on slides by M. Thielscher), *Correctness of SLD Resolution*, Lecture 4 of Foundations of Logic Programming, TU Dresden, 2026, <https://iccl.inf.tu-dresden.de/w/images/3/33/FLP2026-04.pdf>: Theorem 4.4 (a successful SLD derivation of $P \cup \{Q_0\}$ with computed answer substitution $\theta$ gives $P \models Q_0\theta$), with an expression true in an interpretation when its universal closure is (slide 9), algebras with a nonempty domain (slide 5) and Herbrand interpretations over the Herbrand universe (slide 21).
- H. Strass (based on slides by M. Thielscher), *Least Herbrand Models*, Lecture 5 of Foundations of Logic Programming, TU Dresden, 2026, <https://iccl.inf.tu-dresden.de/w/images/8/8b/FLP2026-05.pdf>: Theorem 4.37 (for a ground atom $A$, $M(P) \Vdash A$ if and only if $A$ is in the success set of $P$, the set of ground atoms $A$ for which $P \cup \{A\}$ has a successful SLD derivation) and Theorem 4.29 ($M(P)$ is the least Herbrand model of $P$).
