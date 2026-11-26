# Retroactivity by reset and replay

Every data structure $D$ yields a retroactive version that, after each timeline edit, stores the edited timeline, resets $D$ to its initial state and replays the whole timeline. This implementation is correct: after every admissible edit, the backend's state is the edited timeline replayed from the initial state. If every ordinary operation of $D$ costs at most $c$, an edit on a timeline of length $m$ costs the edit and reset primitives plus at most $c \cdot m$, i.e. $O(m)$ overhead per edit; this is the baseline that efficient retroactive structures improve on (Demaine, Iacono and Langerman show that in general an $\Omega(m)$ overhead can be necessary).

## Proof sketch

Correctness is immediate by induction on the replay. The cost counts one call per replayed operation, each bounded by $c$.

## Depends on

- [Retroactive data structure](retroactive-data-structure.md)

## Sources

- E. D. Demaine, J. Iacono and S. Langerman, "Retroactive Data Structures", ACM Transactions on Algorithms 3(2), 2007.
