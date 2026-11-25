# Registers have consensus number one

There is no wait-free consensus protocol for two processes that uses only atomic read/write registers. The proof is a valency argument: every protocol has a bivalent initial state and a critical bivalent state whose successors are univalent of different valences, and a case analysis of the pending reads and writes of the two processes at that state shows that one process cannot tell the two extensions apart. Hence atomic registers have consensus number $1$.

## Depends on

- [Valency arguments for consensus](valency-arguments-for-consensus.md)
- [Consensus number](consensus-number.md)

## Sources

- M. Herlihy, "Wait-free synchronization", *ACM Transactions on Programming Languages and Systems* 13(1):124–149, 1991, Theorem 2
- Related original result: M. C. Loui and H. H. Abu-Amara, "Memory requirements for agreement among unreliable asynchronous processes", *Advances in Computing Research* 4:163–183, 1987. Herlihy credits Loui and Abu-Amara with similar results beside Theorem 2.
