# The fundamental principle of deadlock

Let $V$ be a [network](networks-of-csp-processes.md) satisfying assumptions (A)–(E) that is free of strong conflict (see [Ungranted requests and conflicts in CSP networks](ungranted-requests-and-conflicts.md)). Then every deadlock state of $V$ contains a proper cycle of ungranted requests: a cycle $P_{i_1}, P_{i_2}, \dots, P_{i_k}, P_{i_1}$ of at least three distinct processes, each with an ungranted request to the next.

## Depends on

- [Networks of CSP processes and deadlock](networks-of-csp-processes.md)
- [Ungranted requests and conflicts in CSP networks](ungranted-requests-and-conflicts.md)

## Sources

- A. W. Roscoe, *The Theory and Practice of Concurrency*, Prentice Hall, 1997; revised edition 2005, author's online version, <https://www.cs.ox.ac.uk/bill.roscoe/publications/68b.pdf>, Section 13.1.2 (the chain of ungranted requests from a process in a deadlock state, which by busy-ness and finiteness repeats) and Section 13.1.3 ("Fundamental principle of deadlock" and the argument before it that freedom from strong conflict excludes $P_n = P_{n+2}$), pp. 341–348.
