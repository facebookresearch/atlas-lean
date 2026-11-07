# Action of the rectangle group on grid cells

Let $n, m \in \mathbb{N}$ and view the cells
of the $n \times m$ grid as $\mathbb{Z}/n\mathbb{Z} \times \mathbb{Z}/m\mathbb{Z}$. Write the
elements of the dihedral group of order $8$ as rotations $r_i$ and reflections $sr_i$ for
$i \in \mathbb{Z}/4\mathbb{Z}$. Each element acts on cells as follows: $r_0$ by the identity,
$r_i$ with $i \ne 0$ by the half-turn $(x, y) \mapsto (-1 - x, -1 - y)$, $sr_0$ by the
reflection $(x, y) \mapsto (-1 - x, y)$, and $sr_i$ with $i \ne 0$ by the reflection
$(x, y) \mapsto (x, -1 - y)$.

The paper's rectangle group $D_4 = \langle r^2, f \rangle$ is the subgroup
$\{r_0, r_2, sr_0, sr_2\}$, with $f = sr_0$, $r^2 = r_2$ and $r^2 f = sr_2$. On this subgroup the
assignment of cell maps is a homomorphism into maps under composition; the values at $r_1$, $r_3$,
$sr_1$ and $sr_3$ are never used.

## Sources

- Peter Kagey, William Keehn, *Counting Tilings of the n × m Grid, Cylinder, and Torus*, Journal of Integer Sequences 27 (2024), Article 24.6.1, Definitions 1.4.1 and 1.4.2 (the dihedral action on cells).
