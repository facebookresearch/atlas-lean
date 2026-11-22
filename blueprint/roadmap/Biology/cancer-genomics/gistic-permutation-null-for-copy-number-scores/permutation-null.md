# GISTIC permutation null distribution

For sample values $x_j(v)$ ($S$ samples, $M$ markers), a marker $m$ and a real $g$, the permutation null probability of $g$ is

$$P_S(g) = \frac{\bigl|\{(\sigma_1, \dots, \sigma_S) : \sum_j x_j(\sigma_j(m)) = g\}\bigr|}{(M!)^S},$$

the probability that the [permuted score](permuted-score.md) at $m$ equals $g$ when $\sigma_1, \dots, \sigma_S$ are independent uniformly random permutations of the markers.
