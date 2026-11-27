# Size-change termination implies termination

If a first-order functional program is [size-change terminating](size-change-graphs.md) for a set of size-change graphs that is safe for its calls, then the program terminates on all inputs. Indeed, a nonterminating evaluation yields an infinite state-transition sequence of calls, whose call sequence lies in $\mathrm{Flow}^\omega$; size-change termination gives a thread with infinitely many $\downarrow$ edges in its multipath, and safety transfers it to an infinitely descending sequence of argument values, contradicting well-foundedness of $\prec$.

## Depends on

- [Size-change graphs and size-change termination](size-change-graphs.md)

## Sources

- P. M. Neergaard, *The Size-Change Principle of Termination*, lecture notes, Brandeis University, <https://www.cs.brandeis.edu/~cs117a/size-change-termination.pdf>, Section 4, Theorem 4.2 with Lemmas 3.7, 4.3 and 4.4.
