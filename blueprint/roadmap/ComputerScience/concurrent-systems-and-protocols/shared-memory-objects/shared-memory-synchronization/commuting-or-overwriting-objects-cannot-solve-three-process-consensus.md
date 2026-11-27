# Commuting-or-overwriting objects cannot solve three-process consensus

Call a set $F = \{f_i\}$ of functions on register values *interfering* (commuting or overwriting) if for every value $v$ and all indices $i, j$ either $f_i(f_j(v)) = f_j(f_i(v))$ (the two functions commute) or one overwrites the other: $f_i(f_j(v)) = f_i(v)$ or $f_j(f_i(v)) = f_j(v)$. There is no wait-free solution to three-process consensus using any combination of read-modify-write operations that apply functions from an interfering set (Herlihy, Theorem 4); in particular none using registers that support any combination of read, write, test-and-set, swap and fetch-and-add. Since a register with any nontrivial read-modify-write operation has consensus number at least $2$ (Herlihy, Theorem 3), the consensus number of test-and-set is exactly $2$.

## Proof sketch

Take a critical bivalent configuration where the next steps of two processes lead to different valences; both must apply read-modify-write operations to the same register. If the functions commute, a third process cannot distinguish the two orders; if $q$'s function overwrites $p$'s, the runs ($p$'s step, then $q$'s) and ($q$'s step alone) leave the register in the same state, so a solo run of a third process yields indistinguishable runs with different decisions. The same argument applies verbatim to any deterministic object whose operations pairwise commute or overwrite on every state, a generalization not stated by Herlihy.

## Depends on

- [Consensus number](../consensus-number.md)
- [The asynchronous shared-memory model](../the-asynchronous-shared-memory-model.md)

## Proof depends on

- [Valency arguments for consensus](../valency-arguments-for-consensus.md)
- [Nontrivial read-modify-write registers solve two-process consensus](../nontrivial-read-modify-write-registers-solve.md)
- [Registers have consensus number one](../registers-have-consensus-number-one.md)

## Sources

- Maurice Herlihy, "Wait-Free Synchronization", ACM Transactions on Programming Languages and Systems 13(1), 1991, §3.2, Theorems 3 and 4.
