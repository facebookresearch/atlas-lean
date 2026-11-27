# Retroactivity by reset and replay

Every data structure $D$ yields a retroactive version that, after each timeline edit, stores the edited timeline, resets $D$ to its initial state and replays the whole timeline. This implementation is correct: after every admissible edit, the backend's state is the edited timeline replayed from the initial state. If every ordinary operation of $D$ costs at most $c$, an edit on a timeline of length $m$ costs the edit and reset primitives plus at most $c \cdot m$, i.e. $O(m)$ overhead per edit; this is the baseline that efficient retroactive structures improve on. Demaine, Iacono and Langerman's rollback method replays only the last $r$ operations for an edit $r$ operations in the past, in $O(r\,T(n))$ time for worst-case operation time $T(n)$, and they show that some data structure with $O(1)$-time operations needs $\Omega(r)$ time per retroactive update or query in the history-dependent algebraic-computation-tree, integer-RAM and generalized real-RAM models, and $\Omega(\sqrt{r / \log r})$ amortized time in the cell-probe model.

## Proof sketch

Correctness is immediate by induction on the replay. The cost counts one call per replayed operation, each bounded by $c$.

## Depends on

- [Retroactive data structure](retroactive-data-structure.md)

## Sources

- E. D. Demaine, J. Iacono and S. Langerman, "Retroactive Data Structures", ACM Transactions on Algorithms 3(2), Article 13, 2007.
