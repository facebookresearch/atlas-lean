# Labelled density

For a graph $G$ on the vertex set $\{0, \dots, k-1\}$ and a function $W$
of two real variables, the labelled density of $G$ in $W$ is

$$\tau(G, W) = \int_{[0,1]^k} \prod_{i < j} w_{ij}(x) \, dx,$$

where the integral is with respect to Lebesgue measure (and is taken to be $0$ if the integrand is
not integrable), the product runs over the pairs $i < j$ of vertices, and $w_{ij}(x) = W(x_i, x_j)$
if $i$ and $j$ are adjacent in $G$ and $w_{ij}(x) = 1 - W(x_i, x_j)$ otherwise.

When $W$ is a graphon, $\tau(G, W)$ is the probability that the $W$-random graph on
$\{0, \dots, k-1\}$ (independent uniform points $x_i \in [0, 1]$, each pair $\{i, j\}$ joined
independently with probability $W(x_i, x_j)$) equals $G$.
