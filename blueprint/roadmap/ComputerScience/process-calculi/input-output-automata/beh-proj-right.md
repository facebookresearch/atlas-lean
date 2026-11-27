# Projection of a behaviour of a composition onto its second component

Let $A_1$ and $A_2$ be [input/output automata](ioautomaton.md) with [strongly compatible](strongly-compatible.md) signatures and $A_1 \| A_2$ their [composition](compose-automata.md). If $\beta$ is a finite [behaviour](beh.md) of $A_1 \| A_2$, then its [projection](proj.md) $\beta|\mathrm{sig}(A_2)$ is a finite behaviour of $A_2$ (Lynch and Tuttle, 1989, Proposition 1, for finite behaviours).

If $\gamma$ is a schedule of the composition with behaviour $\beta$, the projection of $\gamma$ onto the second component is a schedule of it, and its behaviour is the projection of $\beta$.

## Informally uses

- [Projection of a schedule of a composition onto its second component](sched-proj-right.md): the schedule.
- [Projection onto the second component and external projection commute](proj-ext-proj-compose-right.md): the behaviour.

## Sources

- N. A. Lynch, M. R. Tuttle, *An introduction to input/output automata*, CWI Quarterly 2(3), 1989, 219–246: Proposition 1.
