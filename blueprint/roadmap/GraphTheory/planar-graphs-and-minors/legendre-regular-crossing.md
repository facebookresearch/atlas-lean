# Crossing points of the regular drawing of the complete bipartite graph

Let $n$ be a
natural number. In the regular drawing of $K_{n,n}$ in $\mathbb{Q}^2$, the left vertices are the
points $(0, i)$ and the right vertices are the points $(1, j)$ for $0 \le i, j < n$, and each edge
is the straight segment from $(0, i)$ to $(1, j)$. For $i < i'$ and $j' < j$, the edges from
$(0, i)$ to $(1, j)$ and from $(0, i')$ to $(1, j')$ cross at the point $(x, i + x(j - i))$, where
$x = (i' - i)/((i' - i) + (j - j'))$. The number of distinct points obtained in this way, over all
$i, i', j, j' < n$ with $i < i'$ and $j' < j$, equals $S_1 - S_2$, where $S_1$ is the sum of
$(n - a)(n - b)$ over all ordered pairs $(a, b)$ of coprime integers with $1 \le a, b \le n - 1$,
and $S_2$ is the sum of $(n - 2a)(n - 2b)$ over all ordered pairs $(a, b)$ of coprime integers
with $1 \le 2a \le n - 1$ and $1 \le 2b \le n - 1$.

The difference is taken in $\mathbb{N}$; since $S_2 \le S_1$, it is the ordinary difference.

## Sources

- Stéphane Legendre, "The Number of Crossings in a Regular Drawing of the Complete Bipartite Graph", Journal of Integer Sequences 12 (2009), Article 09.5.5, Proposition `count_all`, line 263, <https://cs.uwaterloo.ca/journals/JIS/VOL12/Legendre/legendre2.tex>.
