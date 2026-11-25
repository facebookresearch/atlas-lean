# Counted copy of a square matrix

Given an $n \times n$ matrix $A$ (a vector of $n$ rows,
each a vector of $n$ entries), this computation returns the matrix whose $(i, j)$ entry is
$A_{ij}$, traversing the entries row by row and charging a cost of $(1, (0, 0))$ for each entry,
that is, one logical assignment in the first cost coordinate and nothing in the other two.
