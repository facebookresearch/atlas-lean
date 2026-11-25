# Floating-point interval arithmetic with directed rounding is sound

This node collects interval arithmetic with directed rounding in a binary floating-point format and its enclosure
soundness.

## Expansion

A sound expansion has separate pages for:

1. **Directed rounding.** In a bounded binary format with subnormals, extended by $\pm\infty$, $\mathrm{RD}(x)$ is the largest
   member at most $x$ and $\mathrm{RU}(x)$ the smallest at least $x$; so for $x$ above the largest finite number $\Omega$,
   $\mathrm{RU}(x) = +\infty$ while $\mathrm{RD}(x) = \Omega$, and symmetrically below $-\Omega$.
2. **Endpoint operations.** $[a,b] + [c,d] = [\mathrm{RD}(a+c), \mathrm{RU}(b+d)]$, subtraction likewise, multiplication by
   $[\min_{u \in P} \mathrm{RD}(u), \max_{u \in P} \mathrm{RU}(u)]$ over the set $P$ of the four endpoint products, and division only by intervals not containing $0$; the
   conventions for infinite endpoints are stated, and NaN never arises in valid operations.
3. **Soundness.** Each operation returns an interval containing the exact result set of the real operation on the
   argument intervals; by induction, evaluating an expression encloses its range, as in the exact-arithmetic enclosure
   theorem.

## Depends on

- [Floating-point numbers of a bounded format](../../ComputerScience/algebraic-and-numerical-algorithms/floating-point-rounding/is-float-in.md)

## Proof depends on

- [Fundamental theorem of interval arithmetic and the dependency effect](fundamental-theorem-of-interval-arithmetic-and-the-dependenc.md)

## Related topics

- [Round to nearest, ties to even](../../ComputerScience/algebraic-and-numerical-algorithms/floating-point-rounding/fl.md)

## Sources

- delta-Complete Decision Procedures for Satisfiability over the Reals — S. Gao, J. Avigad, E. M. Clarke, LNAI 7364, 2012, Definitions 4.1 and 4.2 and Example 4.1 (floating-point intervals with infinite endpoints, hulls, interval extensions). <http://www.cs.cmu.edu/~sicung/papers/cade2012.pdf>
