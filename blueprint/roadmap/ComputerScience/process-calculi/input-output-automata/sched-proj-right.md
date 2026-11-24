# Projection of a schedule of a composition onto its second component

Let $A_1$ and $A_2$ be [input/output automata](ioautomaton.md) with [strongly compatible](strongly-compatible.md) signatures and $A_1 \| A_2$ their [composition](compose-automata.md). If $\beta$ is a finite [schedule](sched.md) of $A_1 \| A_2$, then its [projection](proj.md) $\beta|\mathrm{sig}(A_2)$ is a finite schedule of $A_2$ (Lynch and Tuttle, 1989, Proposition 1, for finite schedules).

The projection keeps the actions of the second component, in order.

## Informally uses

- [Projection of an execution of a composition onto its second component](m-tr-proj-right.md): the step-by-step projection.

## Sources

- N. A. Lynch, M. R. Tuttle, *An introduction to input/output automata*, CWI Quarterly 2(3), 1989, 219–246: Proposition 1.
