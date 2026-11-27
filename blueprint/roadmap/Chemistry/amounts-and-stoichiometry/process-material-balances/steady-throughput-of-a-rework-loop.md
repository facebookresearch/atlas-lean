# Steady throughput of a rework loop

Let an operation receive fresh feed $f \ge 0$ and split its output into disjoint good, scrap and rework fractions
$g, s, r \ge 0$ with $g + s + r = 1$, the rework being returned to its input. If $r < 1$, the steady throughput is
$x = f/(1 - r)$, the unique solution of $x = f + r x$, and the good and scrap flows are $g x$ and $s x$, which add up to the
fresh feed $f$. If $r = 1$ and $f > 0$ there is no steady state, and if $r = 1$ and $f = 0$ every throughput is steady. Choosing
the fractions optimally is outside this result.

## Depends on

## Proof depends on

- [Scalar recycle, purge and bypass loop](scalar-recycle-purge-and-bypass-loop.md)

## Sources

- J. B. Rawlings and J. G. Ekerdt, *Chemical Reactor Analysis and Design Fundamentals*, 2nd edition, paperback, seventh printing (November 2026), Nob Hill Publishing; freely distributed by the authors at <https://sites.engineering.ucsb.edu/~jbraw/chemreacfun/> (page numbers below are the printed ones): Section 4.3, Equation 4.36, the species balance with accumulation, flows and production (p. 127).
