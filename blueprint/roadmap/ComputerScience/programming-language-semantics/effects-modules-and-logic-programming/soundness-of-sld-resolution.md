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
