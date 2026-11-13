# Colored Dyck paths and colored polygon partitions

Let
$\gamma = (\gamma_1, \gamma_2, \dots)$ be a sequence of natural numbers. Let $d_{n,k}(\gamma)$ be
the number of Dyck paths of semilength $n$ with $k$ peaks in which each block $UD^j$, formed by a
peak and the maximal run of $D$ steps starting at its $D$, carries one of $\gamma_j$ colors, and
let $p_{n,k}(\gamma)$ be the number of partitions of a rooted convex $(n+2)$-gon by $k - 1$
noncrossing diagonals into $k$ polygons in which each $(j+2)$-gon carries one of $\gamma_j$
colors. For all natural numbers $n$ and $k$ with $1 \le k \le n$,

$$\binom{n+k}{k} d_{n,k}(\gamma) = \binom{n+1}{k} p_{n,k}(\gamma).$$

## Sources

- Gil, Hoover, and Shearer, *Bijections Between Colored Compositions, Dyck Paths, and Polygon Partitions*, Journal of Integer Sequences 27 (2024), Article 24.5.2, Theorem 6 (`jis-2024-24.5.2-thm-6`).
