# Computing a lower envelope by divide and conquer

Let $F = \{f_1, \dots, f_n\}$ be continuous real functions on a common interval, any two of which intersect in at most $s$ points, and assume that the intersections of any two of them can be computed in constant time. Then the lower envelope of $F$, as its envelope sequence with the breakpoints between consecutive pieces, can be constructed in $O(\lambda_s(n) \log n)$ time, by computing the envelopes of two halves recursively and merging them with a sweep over their at most $2\lambda_s(n)$ events.

## Depends on

- [Davenport–Schinzel sequence](davenport-schinzel-sequence.md)
- [Lower envelopes of functions are Davenport–Schinzel sequences](lower-envelopes-of-functions-are-davenport-schinzel-sequences.md)

## Proof depends on

- [Superadditivity of Davenport–Schinzel lengths](superadditivity-of-davenport-schinzel-lengths.md)

## Sources

- *Computational Geometry*, lecture notes, ETH Zürich, autumn 2013, Chapter 12 (Davenport–Schinzel sequences), <https://ti.inf.ethz.ch/ew/courses/CG13/lecture/Chapter%2012.pdf>: Theorem 12.8
