# Commuting-or-overwriting objects cannot solve three-process consensus

Call a family of deterministic shared objects *commuting or overwriting* if any two operations applied by different processes to the same object either commute (leave the object in the same state in either order) or one overwrites the other (applying it last makes the earlier operation invisible). Read/write registers, test-and-set, swap and fetch-and-add are of this kind. No wait-free deterministic protocol using such objects (and registers) solves binary consensus among three or more processes; combined with the two-process test-and-set protocol, the consensus number of test-and-set is exactly $2$.

## Proof sketch

Take a critical bivalent configuration where the next steps of two processes lead to different valences; both must access the same object. If the operations commute, a third process cannot distinguish the two orders; if $q$'s operation overwrites $p$'s, the runs ($p$'s step, then $q$'s) and ($q$'s step alone) leave the object in the same state, so a solo run of a third process yields indistinguishable runs with different decisions.

## Depends on

- [Consensus number](../consensus-number.md)
- [The asynchronous shared-memory model](../the-asynchronous-shared-memory-model.md)

## Proof depends on

- [Valency arguments for consensus](../valency-arguments-for-consensus.md)
- [Nontrivial read-modify-write registers solve two-process consensus](../nontrivial-read-modify-write-registers-solve.md)
- [Registers have consensus number one](../registers-have-consensus-number-one.md)

## Sources

- Maurice Herlihy, "Wait-Free Synchronization", ACM Transactions on Programming Languages and Systems, 1991.
