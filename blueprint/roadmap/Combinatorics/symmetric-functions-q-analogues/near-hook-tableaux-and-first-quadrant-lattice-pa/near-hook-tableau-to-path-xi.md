# The map $\xi$ from near-hook tableaux to lattice paths

Let $n \in \mathbb{N}$ and let
$T$ be a semistandard Young tableau of shape $\theta^{(n)}$, with rows and columns numbered from
$0$; call row $0$ of $\theta^{(n)}$ the arm and the cell in row $1$ and column $1$ the heart, and
let $H$ be the entry of $T$ in the heart. Then $\xi(T)$ is the word $(s_1, \dots, s_{2n+2})$ of
steps in $\mathbb{Z}^2$ given as follows, where $E = (1, 0)$, $N = (0, 1)$, $S = (0, -1)$ and
$W = (-1, 0)$. If $i + 2 < H$, then $s_i$ is $E$ if $i + 1$ is an entry of $T$ in the arm and
$N$ otherwise. If $i + 2 = H$, then $s_i$ is $S$ if $i + 1$ is an entry of $T$ in the arm and
$W$ otherwise. If $i + 2 > H$, then $s_i$ is $E$ if $i + 2$ is an entry of $T$ in the arm and
$N$ otherwise.

For a standard Young tableau the inspected value is never $1$ or $H$, so it lies in exactly one
of the arm and the leg, column $0$; "otherwise" then means that it lies in the leg.

## Sources

- L. Ayres et al., *An Exceptional Equinumerosity of Lattice Paths and Young Tableaux*, Journal of Integer Sequences 28 (2025), Article 25.5.2, Section 4.1, equation (eq:xi).
