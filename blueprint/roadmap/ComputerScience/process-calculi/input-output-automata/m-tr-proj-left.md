# Projection of an execution of a composition onto its first component

Let $A_1$ and $A_2$ be [input/output automata](ioautomaton.md) with [strongly compatible](strongly-compatible.md) signatures and $A_1 \| A_2$ their [composition](compose-automata.md). If a finite sequence of actions $\beta$ labels a finite execution of $A_1 \| A_2$ from $s = (s_1, s_2)$ to $t = (t_1, t_2)$, then the [projection](proj.md) $\beta|\mathrm{sig}(A_1)$ labels a finite execution of $A_1$ from $s_1$ to $t_1$.
