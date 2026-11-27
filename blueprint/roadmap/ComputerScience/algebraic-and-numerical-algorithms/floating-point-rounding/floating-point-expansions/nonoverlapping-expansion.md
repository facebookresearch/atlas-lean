# Nonoverlapping floating-point expansion

Fix a precision $p$. An *expansion* is a finite sum $x = x_n + \dots + x_2 + x_1$ whose *components* $x_i$ are binary floating-point numbers with $p$-bit significands. Two floating-point numbers $x$ and $y$ are *nonoverlapping* if there are integers $r$ and $s$ with $x = r 2^s$ and $|y| < 2^s$, or $y = r 2^s$ and $|x| < 2^s$; that is, the least significant nonzero bit of one is more significant than the most significant nonzero bit of the other. Zero overlaps no number. An expansion is *nonoverlapping* if its components are pairwise nonoverlapping. Two floating-point numbers $x$ and $y$ are *adjacent* if they overlap, or $x$ overlaps $2y$, or $2x$ overlaps $y$, and an expansion is *nonadjacent* if no two of its components are adjacent.

For example, in four-bit arithmetic $1100$ and $-10.1$ are nonoverlapping, while $101$ and $10$ overlap.

## Depends on

- [Binary floating-point numbers](../is-float.md)

## Sources

- J. R. Shewchuk, "Adaptive precision floating-point arithmetic and fast robust geometric predicates", *Discrete & Computational Geometry* 18(3):305–363, 1997; technical report version CMU-CS-96-140R, Section 2.1, the definitions of expansion, nonoverlapping (with the formal version in footnote 2) and adjacent. <https://people.eecs.berkeley.edu/~jrs/papers/robustr.pdf>
