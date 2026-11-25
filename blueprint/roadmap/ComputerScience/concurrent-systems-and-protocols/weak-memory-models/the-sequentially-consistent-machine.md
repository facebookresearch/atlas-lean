# The sequentially consistent machine

In the sequentially consistent machine, a finite number of threads execute programs of loads, stores, fences and atomic read-modify-write instructions over a single shared memory. An execution is an interleaving of the threads' instructions, each executed atomically against the shared memory, in program order within each thread; memory starts from a given initial valuation, and a load returns the value of the most recent store to its location in the interleaving, or the initial value if there is none.

## Depends on

- [The asynchronous shared-memory model](../shared-memory-objects/the-asynchronous-shared-memory-model.md)

## Sources

- P. Sewell, S. Sarkar, S. Owens, F. Zappa Nardelli and M. O. Myreen, "x86-TSO: a rigorous and usable programmer's model for x86 multiprocessors", *Communications of the ACM* 53(7):89–97, 2010
- L. Lamport, "How to make a multiprocessor computer that correctly executes multiprocess programs", *IEEE Transactions on Computers* C-28(9):690–691, 1979
