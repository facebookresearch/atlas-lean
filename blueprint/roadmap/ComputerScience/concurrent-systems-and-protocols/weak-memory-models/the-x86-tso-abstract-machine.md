# The x86-TSO abstract machine

The storage subsystem of the x86-TSO abstract machine has a total map of shared memory, one FIFO store buffer per thread, and one global lock. A thread is *blocked* while another thread holds the lock. The storage subsystem has the following steps.

- A thread $p$ that is not blocked reads $v$ at address $a$ from its own buffer if the newest buffered write of $p$ to $a$ writes $v$, and otherwise, when $p$ has no buffered write to $a$, reads the value of $a$ in memory.
- A thread may append a write to its buffer at any time.
- A thread that is not blocked may remove the oldest write from its buffer and perform it on memory.
- A thread may execute MFENCE only when its buffer is empty.
- A thread may begin a locked instruction only if the lock is free and its buffer is empty; it then acquires the lock. It may end the instruction only if it holds the lock and its buffer is empty; it then releases the lock.

Reads and fences do not change storage state. Enqueuing changes only the thread's buffer, flushing changes that buffer and the addressed memory cell, and lock acquisition and release change only lock ownership. The empty-buffer condition for acquisition is from the formal lock rule; it is not explicit in rule 6 of the later prose summary. These rules do not specify instruction execution, initial states, or progress.

## Sources

- P. Sewell, S. Sarkar, S. Owens, F. Zappa Nardelli and M. O. Myreen, "x86-TSO: a rigorous and usable programmer's model for x86 multiprocessors", *Communications of the ACM* 53(7):89–97, 2010, [Section 3.1, rules 1–7](https://www.cl.cam.ac.uk/~pes20/weakmemory/cacm.pdf).
- S. Owens, S. Sarkar and P. Sewell, "A better x86 memory model: x86-TSO", *TPHOLs 2009*, LNCS 5674:391–407, [Figure 2, lock rule](https://www.cl.cam.ac.uk/~pes20/weakmemory/x86tso-paper.tphols.pdf).
