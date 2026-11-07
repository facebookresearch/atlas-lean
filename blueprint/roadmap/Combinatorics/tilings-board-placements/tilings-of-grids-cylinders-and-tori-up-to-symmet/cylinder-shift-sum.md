# Cylinder shift sum

Let $T$ be a finite set of tile designs, let $n, m \ge 1$, let $g$ be
a map from the cells $\mathbb{Z}/n \times \mathbb{Z}/m$ to themselves, and let $\sigma$ be a
permutation of $T$. The cylinder shift sum of $g$ and $\sigma$ is the sum, over all shifts
$a \in \mathbb{Z}/n$, of the number of tilings $F : \mathbb{Z}/n \times \mathbb{Z}/m \to T$
with $F(g(x + a, y)) = \sigma(F(x, y))$ for every cell $(x, y)$.

The shift is applied before $g$, following the paper's right-action convention, and $\sigma$
is the action of $g$ on tile designs.

## Sources

- Peter Kagey, William Keehn, *Counting Tilings of the n × m Grid, Cylinder, and Torus*, Journal of Integer Sequences 27 (2024), Article 24.6.1, Setting.
