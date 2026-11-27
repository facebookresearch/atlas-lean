# A saturated cell-indicator regression reproduces cell means

Let observations $i = 1, \dots, n$ belong to cells $c = 1, \dots, C$, and regress $y$ without intercept on the $C$ cell indicators. For every nonempty cell, the least-squares fitted value of each of its observations is the cell mean, and every least-squares coefficient vector gives that cell's indicator the cell mean as its coefficient. The indicator column of an empty cell is zero, so its coefficient is arbitrary among least-squares solutions; it is not identified. Proof: $X^{\mathsf T}X$ is diagonal with the cell counts on the diagonal, and $X^{\mathsf T}y$ has the cell sums.

## Proof depends on

- [Least-squares fitted values are the orthogonal projection onto the column space](fitted-values-are-the-orthogonal-projection.md): least-squares solutions are exactly the solutions of the normal equations, with a unique fitted vector.

## Sources

- The statement is derived on this page from its definitions and the linked results; no external source is followed.
