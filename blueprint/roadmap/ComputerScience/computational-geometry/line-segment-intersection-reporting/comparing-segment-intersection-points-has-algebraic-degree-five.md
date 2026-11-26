# Comparing segment intersection points has algebraic degree five

For segments given by the Cartesian coordinates of their endpoints, the predicate that compares the intersection points of two pairs of segments lexicographically has algebraic degree five. Consequently, with input coordinates that are integers of absolute value at most $2^b$, it can be evaluated exactly with integers of about $5b$ bits, which limits exact evaluation in IEEE double precision to coordinates up to about $2^{10}$.

## Depends on

- [The orientation predicate has algebraic degree two](the-orientation-predicate-has-algebraic-degree-two.md)

## Sources

- *Computational Geometry*, lecture notes, ETH Zürich, autumn 2013, Chapter 5 (Line sweep), <https://ti.inf.ethz.ch/ew/courses/CG13/lecture/Chapter%205.pdf>: Proposition 5.15 and the remark after it on the coordinate range for exact evaluation in double precision
