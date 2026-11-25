# GeneGISTIC null

Let $S, W, n$ be natural numbers and $x_j$ real values on $W + n$ markers for each sample $j$, and let $y_j(i)$ be the [window minimum](window-min.md) of $x_j$ starting at $i$, for $0 \le i < W$. Then for every window $i$ and every real $g$, the [permutation null](permutation-null.md) of the values $y_j$ at $i$ is

$$P_S(g) = \frac{N_y(g)}{W^S},$$

where $N_y$ is the [score count](score-count.md) of the values $y_j$ (Mermel et al. 2011).

## Sources

- C. H. Mermel et al., *GISTIC2.0 facilitates sensitive and confident localization of the targets of focal somatic copy-number alteration in human cancers*, Genome Biol. 12 (2011), R41.
