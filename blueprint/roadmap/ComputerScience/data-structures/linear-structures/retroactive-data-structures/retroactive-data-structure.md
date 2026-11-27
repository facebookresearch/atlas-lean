# Retroactive data structure

A *retroactive* version of a data structure with operations $\mathsf{Op}$ maintains a *timeline*, a finite sequence of update operations $o_1, \dots, o_m$, and supports retroactive edits $\mathrm{Insert}(t, o)$, inserting update $o$ at time $t$, and $\mathrm{Delete}(t)$, removing the operation at time $t$. Its state at time $t$ is the result of applying the timeline's updates before $t$, in order, to the initial state. A *partially retroactive* structure answers queries about the present state; a *fully retroactive* one answers queries about the state at any time. An edit is admissible only if the whole edited timeline is admissible, since an edit can invalidate later operations.

## Depends on

- [State-transition specification of a data structure](../../data-structure-interfaces-and-refinement/state-transition-specification.md)

## Sources

- E. D. Demaine, J. Iacono and S. Langerman, "Retroactive Data Structures", ACM Transactions on Algorithms 3(2), Article 13, 2007.
