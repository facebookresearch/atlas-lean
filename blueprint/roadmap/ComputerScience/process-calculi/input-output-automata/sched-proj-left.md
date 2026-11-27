# Projection of a schedule of a composition onto its first component

Let $A_1$ and $A_2$ be [input/output automata](ioautomaton.md) with [strongly compatible](strongly-compatible.md) signatures and $A_1 \| A_2$ their [composition](compose-automata.md). If $\beta$ is a finite [schedule](sched.md) of $A_1 \| A_2$, then its [projection](proj.md) $\beta|\mathrm{sig}(A_1)$ is a finite schedule of $A_1$ (Lynch and Tuttle, 1989, Proposition 1, for finite schedules).

The projection keeps the actions of the first component, in order: Lynch and Tuttle's $\beta | A_1$. Its proof projects a finite execution of the composition, step by step, to one of the component.

## Informally uses

- [Projection of an execution of a composition onto its first component](m-tr-proj-left.md): the step-by-step projection.

## Sources

- N. A. Lynch, M. R. Tuttle, *An introduction to input/output automata*, CWI Quarterly 2(3), 1989, 219–246: Proposition 1.
