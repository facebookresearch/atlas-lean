# Vector-time criterion for consistent cuts

Let $E$ be a finite causally well-formed unicast execution with vector clocks $\mathrm{vc}$, and choose for each process $p$ a frontier event $c_p$ of $p$. The cut whose events are those up to $c_p$ on each process is consistent (closed under happens-before predecessors) if and only if $\mathrm{vc}(c_q)[p] \le \mathrm{vc}(c_p)[p]$ for all processes $p, q$; equivalently, the componentwise supremum of the frontier timestamps equals $(\mathrm{vc}(c_p)[p])_p$.

## Proof sketch

$\mathrm{vc}(c_q)[p]$ counts the events of $p$ in the causal past of $c_q$; the cut is consistent iff each such past is contained in $p$'s part of the cut, i.e. this count does not exceed $p$'s own count at $c_p$.

## Depends on

- [Consistent cuts and their lattice](../consistent-cuts-and-their-lattice.md)
- [Vector timestamps of an execution](../../vector-clocks/timestamps.md)

## Proof depends on

- [Vector clocks characterize happened-before](../../vector-clocks/happens-before-iff-lt.md)

## Sources

- Friedemann Mattern, "Virtual Time and Global States of Distributed Systems", Parallel and Distributed Algorithms, North-Holland, 1989.
