# Polynomial-time recovery of a rational number from a binary prefix

Let $N \ge 1$ and let $j/r$ be a fraction with $0 \le j < r \le N$ in lowest terms. Given the first $\lceil 2\log_2 N \rceil$ fractional bits of $j/r$ (i.e. the dyadic cell of width at most $1/N^2$ containing $j/r$), the pair $(j, r)$ is uniquely determined and can be recovered in time polynomial in $\log N$, for instance by the continued-fraction expansion of the midpoint of that cell: $j/r$ is the unique fraction with denominator at most $N$ in that cell, and it is a convergent of the cell's midpoint.

## Proof sketch

Two distinct fractions with denominators at most $N$ differ by at least $1/N^2$, so a half-open cell of width at most $1/N^2$ contains at most one. The midpoint $x$ of the cell satisfies $|x - j/r| \le 1/(2N^2) \le 1/(2r^2)$, so $j/r$ is a convergent of $x$, found by the Euclidean algorithm in $O(\log N)$ steps.

## Depends on

- [Continued fractions recover the fraction in Shor's algorithm](../../quantum-algorithms/shor-s-order-finding-algorithm/exists-convergent-eq-of-abs-sub-le.md)
- [The complexity class P](../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/p.md)

## Proof depends on

- [Continued fractions recover the fraction in Shor's algorithm](../../quantum-algorithms/shor-s-order-finding-algorithm/exists-convergent-eq-of-abs-sub-le.md)

## Sources

- S. Arora and B. Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009.
- G. H. Hardy and E. M. Wright, "An Introduction to the Theory of Numbers", 6th ed., Oxford University Press, 2008.
