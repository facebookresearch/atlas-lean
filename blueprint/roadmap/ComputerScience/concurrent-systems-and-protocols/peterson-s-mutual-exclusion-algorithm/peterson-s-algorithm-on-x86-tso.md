# Peterson's algorithm on x86-TSO

Peterson's two-thread mutual-exclusion algorithm, correct under sequential consistency, violates mutual exclusion on the x86-TSO machine: each thread's stores to its flag and to the turn variable can remain in its FIFO store buffer while it reads the other thread's flag from shared memory, so both threads can read the other's flag as unset and enter the critical section, as in the store-buffering litmus test. An MFENCE flushes the executing thread's store buffer. If in each thread an MFENCE separates every load from every earlier store of that thread, then every x86-TSO execution has a memory order satisfying the sequential-consistency constraints. For Peterson's algorithm with critical and noncritical sections that do not access shared memory, one MFENCE after the two stores of the entry protocol gives this, so mutual exclusion holds as under sequential consistency.

## Depends on

- [Mutual exclusion in Peterson's algorithm](mutual-exclusion.md)

## Expansion

This page becomes ready once these prerequisites are stated:

- The x86-TSO abstract machine (statement prerequisite)

## Sources

- P. Sewell, S. Sarkar, S. Owens, F. Zappa Nardelli and M. O. Myreen, "x86-TSO: a rigorous and usable programmer's model for x86 multiprocessors", *Communications of the ACM* 53(7):89–97, 2010, the store-buffering (SB) example and the x86-TSO abstract machine with FIFO store buffers and MFENCE, <https://www.cl.cam.ac.uk/~pes20/weakmemory/cacm.pdf>
- A. Linden and P. Wolper, "A verification-based approach to memory fence insertion in relaxed memory systems", *SPIN 2011*, LNCS 6823, Springer, 2011, Section 4, Lemma 1, and the Peterson experiments of Section 6, <https://orbi.uliege.be/bitstream/2268/91581/1/LW%20SPIN2011.pdf>
- G. L. Peterson, "Myths about the mutual exclusion problem", *Information Processing Letters* 12(3):115–116, 1981
