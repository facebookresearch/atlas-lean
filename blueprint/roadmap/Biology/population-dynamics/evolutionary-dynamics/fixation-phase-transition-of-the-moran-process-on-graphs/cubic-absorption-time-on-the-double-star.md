# Cubic absorption time of the Moran process on the double star

For an integer $k \ge 1$, the *double star* $D_k$ has vertex set $L_1 \cup L_2 \cup \{x_1, x_2\}$ with $|L_1| = |L_2| = k$; every vertex of $L_i$ is joined to the centre $x_i$, and $x_1$ is joined to $x_2$. Thus $|V(D_k)| = 2k+2$ and $D_k$ consists of two $k$-leaf stars joined at their centres.

**Theorem.** Let $r > 1$ and let the Moran process (reproducer chosen proportional to fitness, offspring placed on a uniformly random neighbour) on $D_k$ start from a single mutant of fitness $r$ at a uniformly random vertex. Then the expected absorption time (time to fixation or extinction) is at least

$$
\frac{(r-1)^2}{2^5 r^4}\,|V(D_k)|^3 .
$$

## Expansion

Each star is a barrier: the expected one-step change of the potential $\sum_{v \in S} 1/d(v)$ across the bridge $x_1x_2$ is of order $1/n^2$. Once one star is mostly mutant, the second star is invaded only through the centre edge, and the walk across this bottleneck takes order $n^3$ steps. The bound shows that the general upper bound $n^{3+o(1)}$ on the expected absorption time on connected undirected graphs (same paper, Theorem 1) cannot be improved beyond the $o(1)$ in the exponent.

## Sources

- Leslie Ann Goldberg, John Lapinskas and David Richerby, *Phase Transitions of the Moran Process and Algorithmic Consequences*, arXiv:1804.02293, Theorem 44 (Section 5). <https://doi.org/10.48550/arXiv.1804.02293> Published version: Random Structures & Algorithms 56 (2019) 597–647, <https://doi.org/10.1002/rsa.20890>.
