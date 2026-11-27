# Comparing segment intersection points needs only polynomials of degree at most five

For segments given by the Cartesian coordinates of their endpoints, consider two pairs of segments, the two segments of each pair lying on lines of distinct slopes (neither identical nor parallel) and meeting in a point; pairs on identical or parallel lines are sorted out first, their intersection, if any, being an endpoint or a segment. The predicate that compares the two intersection points lexicographically is decided by the signs of polynomials of degree at most five in the input coordinates: writing the $x$-coordinate of each intersection point as a quotient $N_i/D_i$ of polynomials of degrees $3$ and $2$, the comparison is decided by the signs of $N_1 D_2 - N_2 D_1$, $D_1$ and $D_2$ (and similarly for the $y$-coordinates). Consequently, with input coordinates that are integers of absolute value at most $2^b$, it can be evaluated exactly with integers of about $5b$ bits, which limits exact evaluation in IEEE double precision to coordinates up to about $2^{10}$.

## Depends on

- [The orientation predicate has algebraic degree two](the-orientation-predicate-has-algebraic-degree-two.md)

## Sources

- *Computational Geometry*, lecture notes, ETH Zürich, autumn 2013, Chapter 5 (Line sweep), <https://ti.inf.ethz.ch/ew/courses/CG13/lecture/Chapter%205.pdf>: Proposition 5.15 (degree five; the notes also assert, without proof, that no lower degree suffices, which this page does not claim) and the remark after it on the coordinate range for exact evaluation in double precision
