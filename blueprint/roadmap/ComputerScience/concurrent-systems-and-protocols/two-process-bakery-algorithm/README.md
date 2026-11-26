# Two-process bakery algorithm

Lamport's bakery algorithm for two processes, as a model of its own: each process takes a ticket
larger than the one it read from the other, and enters its critical section when its
(ticket, process) pair comes first. Mutual exclusion is stated as an LTL property of every infinite
run. The algorithm for $N$ processes is the topic [Bakery algorithm](../bakery-algorithm/README.md).

- [Proc](proc.md)
- [Other](other.md)
- [PC](pc.md)
- [State of the two-process bakery algorithm](state.md)
- [Ticket order of the two-process bakery algorithm](before.md)
- [Can Enter](can-enter.md)
- [Step](step.md)
- [Bakery](bakery.md)
- [Initial](initial.md)
- [Choosing](choosing.md)
- [Holding](holding.md)
- [Checked](checked.md)
- [Inv](inv.md)
- [Inv step](inv-step.md)
- [Mutex of inv](mutex-of-inv.md)

## Mutual exclusion in LTL

- [Atom](atom.md)
- [Valuation](valuation.md)
- [Mutual exclusion for the two-process bakery algorithm](bakery-mutex.md)
