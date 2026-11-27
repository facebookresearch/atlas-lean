# Retroactivity by the rollback method

Every RAM data structure whose operations each take $T(n)$ worst-case time has a partially retroactive version that supports its operations in the present in $O(T(n))$ time and retroactive edits in $O(r\,T(n))$ time, where $r$ is the number of operations after the time of the edit (Demaine, Iacono and Langerman, Theorem 1). This is the *rollback method*: the structure logs every change each operation makes so that the change can be reversed; for an edit at a time followed by $r$ operations it rolls back those $r$ operations, applies the edit as if it were the present, and re-performs the $r$ operations, which may now act differently. After every admissible edit, the resulting state is that of the edited timeline. This is the baseline that efficient retroactive structures improve on: some data structure with $O(1)$-time operations needs $\Omega(r)$ time, worst case and amortized, for retroactive updates or queries in the history-dependent algebraic-computation-tree, integer-RAM and generalized real-RAM models (Theorem 2), and $\Omega(\sqrt{r / \log r})$ amortized time in the cell-probe model (Theorem 3).

## Proof sketch

Correctness holds because rolling back $r$ operations restores the state before them and re-performing them after the edit replays the edited timeline from that state. Each rolled-back or re-performed operation changes at most $O(T(n))$ memory cells, so an edit costs $O(r\,T(n))$. Derived, not stated in this form by the source: resetting to the initial state and replaying the whole edited timeline of length $m$ instead is the case $r = m$, with $O(m\,T(n))$ time per edit.

## Depends on

- [Retroactive data structure](retroactive-data-structure.md)

## Sources

- E. D. Demaine, J. Iacono and S. Langerman, "Retroactive Data Structures", ACM Transactions on Algorithms 3(2), Article 13, 2007 (Section 3: Theorems 1, 2 and 3).
