# Commuting-or-overwriting objects cannot solve three-process consensus

Call a family of deterministic shared objects *commuting or overwriting* if any two operations applied by different processes to the same object either commute (yield the same state and responses in either order) or one overwrites the other (applying it last makes the earlier operation invisible). Read/write registers, test-and-set, swap and fetch-and-add are of this kind. No wait-free deterministic protocol using such objects (and registers) solves binary consensus among three or more processes; combined with the two-process test-and-set protocol, the consensus number of test-and-set is exactly $2$.

## Proof sketch

Take a critical bivalent configuration where the next steps of two processes lead to different valences; both must access the same object. If the operations commute, a third process cannot distinguish the two orders; if one overwrites the other, running the overwriting process first and then a solo third process yields indistinguishable runs with different decisions.

## Depends on

- [Consensus number](../shared-memory-objects/consensus-number.md)
- [The asynchronous shared-memory model](../shared-memory-objects/the-asynchronous-shared-memory-model.md)

## Proof depends on

- [Valency arguments for consensus](../shared-memory-objects/valency-arguments-for-consensus.md)
- [Nontrivial read-modify-write registers solve two-process consensus](../shared-memory-objects/nontrivial-read-modify-write-registers-solve.md)
- [Registers have consensus number one](../shared-memory-objects/registers-have-consensus-number-one.md)

## Sources

- Maurice Herlihy, "Wait-Free Synchronization", ACM Transactions on Programming Languages and Systems, 1991.
