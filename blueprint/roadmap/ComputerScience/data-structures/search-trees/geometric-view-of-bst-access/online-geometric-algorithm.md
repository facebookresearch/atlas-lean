# Online arborally satisfying algorithms

An *online arborally satisfying algorithm* processes the rows of $P(X)$ in increasing time order and, after seeing $(x_t, t)$ but not later accesses, adds a finite set of points in row $t$ so that the union of all rows added so far, together with $P(X)$ restricted to times $\le t$, is arborally satisfied. Its cost on $X$ is the total number of points in the output.

## Depends on

- [Arborally satisfied point sets](arborally-satisfied-set.md)

## Sources

- Erik D. Demaine, Dion Harmon, John Iacono, Daniel Kane, Mihai Pătraşcu, "The Geometry of Binary Search Trees", SODA (2009).
