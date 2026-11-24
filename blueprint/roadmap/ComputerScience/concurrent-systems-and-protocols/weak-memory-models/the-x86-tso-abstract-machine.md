# The x86-TSO abstract machine

In the x86-TSO abstract machine, each hardware thread $p$ has a FIFO store buffer between it and a shared memory, and there is one global lock. A thread is *blocked* while another thread holds the lock. The machine takes the following steps, and no others.

- A thread $p$ that is not blocked reads $v$ at address $a$ from its own buffer if the newest buffered write of $p$ to $a$ writes $v$, and otherwise, when $p$ has no buffered write to $a$, reads the value of $a$ in memory.
- A thread may append a write to its buffer at any time.
- A thread that is not blocked may remove the oldest write from its buffer and perform it on memory.
- A thread may execute MFENCE only when its buffer is empty.
- A thread may begin a LOCK'd instruction, acquiring the lock, only when the lock is not held and its buffer is empty, and may end it, releasing the lock, only when it holds the lock and its buffer is empty.

## Sources

- P. Sewell, S. Sarkar, S. Owens, F. Zappa Nardelli and M. O. Myreen, "x86-TSO: a rigorous and usable programmer's model for x86 multiprocessors", *Communications of the ACM* 53(7):89–97, 2010, Section 3.1, rules 1–7
