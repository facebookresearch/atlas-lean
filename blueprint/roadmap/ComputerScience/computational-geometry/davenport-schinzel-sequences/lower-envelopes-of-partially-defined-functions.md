# Lower envelopes of partially defined functions

Let $F$ be a collection of $n$ continuous real functions, each defined on a closed real interval, any two of which intersect in at most $s$ points. Then the envelope sequence of the lower envelope of $F$ (defined as for [functions on a common interval](lower-envelopes-of-functions-are-davenport-schinzel-sequences.md), over each maximal interval of the union of the domains, the minimum taken over the functions defined at each point), read from left to right, is an $(n, s + 2)$-Davenport–Schinzel sequence. If two indices $a, b$ alternated $s + 4$ times, then dropping the first and last of the corresponding witness points would leave $s + 2$ alternating witnesses at which both $f_a$ and $f_b$ are defined, with alternately $f_a < f_b$ and $f_b < f_a$, and continuity on their common interval would give $s + 1$ intersections. In particular the lower envelope of $n$ line segments in the plane, none vertical and any two meeting in at most one point, consists of at most $\lambda_3(n)$ pieces.

## Depends on

- [Davenport–Schinzel sequence](davenport-schinzel-sequence.md)
- [Lower envelopes of functions are Davenport–Schinzel sequences](lower-envelopes-of-functions-are-davenport-schinzel-sequences.md)

## Sources

- D. Halperin and M. Sharir, "Arrangements", Chapter 28 of *Handbook of Discrete and Computational Geometry*, 3rd ed., J. E. Goodman, J. O'Rourke and C. D. Tóth (eds.), CRC Press, 2017, <https://doi.org/10.1201/9781315119601>: Section 28.10, for partially defined functions the envelope has complexity at most $\lambda_{s+2}(n)$, so at most $\lambda_3(n)$ pieces for $n$ segments; also Theorem 28.2.1
- *Computational Geometry*, lecture notes, ETH Zürich, autumn 2013, Chapter 12 (Davenport–Schinzel sequences), <https://ti.inf.ethz.ch/ew/courses/CG13/lecture/Chapter%2012.pdf>: Proposition 12.4. Its proof extends each function by nearly vertical rays, which works for segments but not for arbitrary continuous functions (a function oscillating like $\sqrt t \sin(1/t)$ near the endpoint of another meets every such ray infinitely often); the direct alternation count above avoids this
