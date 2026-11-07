# Torus shift sum

Let $n, m \ge 1$, let $T$ be a finite set of tile designs, let $g$ be a
map from $\mathbb{Z}/n \times \mathbb{Z}/m$ (the cells of the $n \times m$ torus) to itself and
let $\sigma$ be a permutation of $T$. For a shift $(a, b) \in \mathbb{Z}/n \times \mathbb{Z}/m$,
count the tilings $F \colon \mathbb{Z}/n \times \mathbb{Z}/m \to T$ with
$F(g(x + a, y + b)) = \sigma(F(x, y))$ for every cell $(x, y)$. The torus shift sum is the sum of
these counts over all $nm$ shifts $(a, b)$.

Shifting the cell first and applying $g$ afterwards follows the right-action convention of the
source; shifts act trivially on tile designs.

## Sources

- Peter Kagey, William Keehn, *Counting Tilings of the n × m Grid, Cylinder, and Torus*, Journal of Integer Sequences 27 (2024), Article 24.6.1, Setting.
