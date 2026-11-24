# Pasting schedules of the components of a composition

Let $A_1$ and $A_2$ be [input/output automata](ioautomaton.md) with [strongly compatible](strongly-compatible.md) signatures and $A_1 \| A_2$ their [composition](compose-automata.md). A finite sequence $\beta$ of actions of $A_1 \| A_2$ whose projections $\beta|\mathrm{sig}(A_1)$ and $\beta|\mathrm{sig}(A_2)$ are finite schedules of $A_1$ and $A_2$ is a finite schedule of $A_1 \| A_2$ (Lynch and Tuttle, 1989, Proposition 3, for two automata and finite schedules). With [the projection of schedules](sched-proj-left.md) this characterizes the finite schedules of a composition by those of its components.

## Informally uses

- [Pasting executions of the components of a composition](m-tr-of-proj.md): the executions behind the two schedules are pasted along $\beta$.
- [Actions of a composed signature](acts-compose.md): the actions of the composition are those of the components.

## Sources

- N. A. Lynch, M. R. Tuttle, *An introduction to input/output automata*, CWI Quarterly 2(3), 1989, 219–246: Proposition 3.
