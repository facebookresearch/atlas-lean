# FIFO queues have consensus number two

A FIFO queue together with atomic registers solves wait-free consensus for two processes: initialize the queue with a "winner" token followed by a "loser" token; each process writes its input to a register and dequeues, deciding its own input on dequeuing the winner token and the other's input otherwise. There is no wait-free consensus protocol for three processes from FIFO queues and registers. Hence FIFO queues have consensus number $2$.

## Depends on

- [Valency arguments for consensus](valency-arguments-for-consensus.md)
- [Consensus number](consensus-number.md)

## Sources

- M. Herlihy, "Wait-free synchronization", *ACM Transactions on Programming Languages and Systems* 13(1):124–149, 1991, Theorems 6 and 7
