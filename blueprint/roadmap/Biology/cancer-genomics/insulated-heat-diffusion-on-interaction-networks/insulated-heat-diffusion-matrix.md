# Insulated heat diffusion matrix

Let $G = (V, E)$ be a finite undirected graph on $V = \{1, \dots, n\}$ with no isolated vertices, and let $W$ be the normalized adjacency matrix

$$W_{ij} = \begin{cases} 1/\deg(j), & \{i, j\} \in E, \\ 0, & \text{otherwise.} \end{cases}$$

For an insulating parameter $\beta \in (0, 1]$, the insulated heat diffusion matrix is

$$F = \beta \bigl(I - (1 - \beta) W\bigr)^{-1} .$$

Then:

1. $I - (1-\beta)W$ is invertible and $F = \beta \sum_{t \ge 0} (1 - \beta)^t W^t$;
2. $F$ is entrywise nonnegative and each column of $F$ sums to $1$;
3. $F_{ij}$ is the probability that a random walk started at $j$, which at each step stops with probability $\beta$ and otherwise moves to a uniformly chosen neighbour, stops at $i$ (random walk with restart);
4. $F_{ij} \deg(j) = F_{ji} \deg(i)$ for all $i, j$; in particular $F$ is in general not symmetric.

$F_{ij}$ is interpreted as the heat on vertex $i$ at equilibrium when a unit heat source is placed on $j$: each vertex passes heat to its neighbours but retains the fraction $\beta$.

## Expansion

Every column of $W$ sums to $1$, so $\|(1-\beta)W\|_1 = 1 - \beta < 1$ for $\beta > 0$ and the Neumann series converges, giving (1). Nonnegativity and column sums follow termwise, since $W^t$ is column-stochastic and $\beta \sum_t (1-\beta)^t = 1$. The term $\beta (1-\beta)^t (W^t)_{ij}$ is the probability that the walk takes exactly $t$ steps and is then at $i$, giving (3). For (4), write $W = A D^{-1}$ with $A$ the adjacency matrix and $D = \operatorname{diag}(\deg)$; then $W^t D = (A D^{-1})^{t-1} A$ is symmetric for every $t \ge 1$ (and equals $D$ for $t = 0$), hence $F D$ is symmetric. In HotNet2, $\beta$ is chosen from the network alone, independently of mutation data; because $F$ depends only on the graph, it is computed once per network.

## Sources

- M. D. M. Leiserson, F. Vandin, H.-T. Wu, J. R. Dobson, J. V. Eldridge, et al., "Pan-cancer network analysis identifies combinations of rare somatic mutations across pathways and protein complexes", *Nature Genetics* 47 (2015), 106–114, Online Methods "Heat Diffusion" and Supplementary Note Section 1.2 (random walk with restart), <https://doi.org/10.1038/ng.3168> (PMC4444046).
