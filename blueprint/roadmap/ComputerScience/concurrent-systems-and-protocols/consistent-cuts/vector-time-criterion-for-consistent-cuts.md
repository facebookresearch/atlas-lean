# Vector-time criterion for consistent cuts

Let $X$ be a cut of a finite execution of a finite set $P$ of processes, with last event $c_p$ on each process $p$, and let $\mathrm{vc}(e) \in \mathbb{N}^P$ be the vector timestamps that the vector clock algorithm assigns to the events $e$. Then $X$ is consistent (closed under happens-before predecessors) if and only if $\mathrm{vc}(c_q)[p] \le \mathrm{vc}(c_p)[p]$ for all processes $p, q$; equivalently, if and only if the componentwise supremum of the timestamps $\mathrm{vc}(c_p)$, $p \in P$, equals $(\mathrm{vc}(c_p)[p])_p$.

The execution need not be causally well formed or unicast: a message may be received more than once, by several events.

## Proof sketch

$\mathrm{vc}(c_q)[p]$ counts the events of $p$ in the causal past of $c_q$; the cut is consistent iff each such past is contained in $p$'s part of the cut, i.e. this count does not exceed $p$'s own count at $c_p$.

## Sources

- Friedemann Mattern, "Virtual Time and Global States of Distributed Systems", Parallel and Distributed Algorithms, North-Holland, 1989.
