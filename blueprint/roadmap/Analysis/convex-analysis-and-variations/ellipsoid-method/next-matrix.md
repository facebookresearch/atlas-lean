# Matrix after a central-cut step

The new matrix of the central-cut step in dimension $n$ is

$$
A' = \frac{n^2}{n^2 - 1}\Bigl(A - \frac{2}{n+1}\, b b^\top\Bigr), \qquad b = \frac{A c}{\sqrt{c^\top A c}} .
$$

The ellipsoid shrinks by the factor $\frac{n}{n+1}$ along $b$ and stretches by $\frac{n}{\sqrt{n^2-1}}$ in the orthogonal directions.

## Sources

- M. X. Goemans, *Lecture notes on the ellipsoid algorithm*, MIT 18.433 Combinatorial Optimization, Handout 19 (4 May 2009), <https://math.mit.edu/~goemans/18433S09/ellipsoid.pdf>, equation (5) and step 2 of the algorithm.
