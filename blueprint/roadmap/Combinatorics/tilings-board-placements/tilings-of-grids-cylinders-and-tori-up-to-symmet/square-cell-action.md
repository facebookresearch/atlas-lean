# The dihedral action on the cells of the square grid

For a natural number $n$, let $r$ and
$f$ be the maps of $(\mathbb{Z}/n\mathbb{Z})^2$ given by $r(x, y) = (-1 - y, x)$ (the quarter-turn)
and $f(x, y) = (-1 - x, y)$ (the reflection). The dihedral group of order $8$ has the rotations
$r_i$ and the reflections $sr_i$ for $i \in \mathbb{Z}/4\mathbb{Z}$. The action sends $r_i$ to the
$i$-fold iterate $r^i$ and $sr_i$ to $f \circ r^i$, where $i$ is read as an integer in
$\{0, 1, 2, 3\}$.

Since $f \circ r \circ f = r^{-1}$ on cells, this assignment turns the multiplication of the
dihedral group into composition of maps.

## Sources

- Peter Kagey, William Keehn, *Counting Tilings of the n × m Grid, Cylinder, and Torus*, Journal of Integer Sequences 27 (2024), Article 24.6.1, Definition 1.4.2 (the dihedral action on cells).
