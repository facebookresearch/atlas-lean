# Weighted mean

For a finite set $\iota$ and real vectors $v, a \in \mathbb{R}^\iota$, the weighted mean of $a$ with weights $v$ is

$$\bar a_v = \frac{\sum_j v_j a_j}{\sum_j v_j},$$

with the convention $x/0 = 0$.

In demography, with real category sizes $N_i$ and rates $T_i$ indexed by $\iota$ (for example age
groups), the weighted mean $(\sum_i N_i T_i) / \sum_i N_i$ of the rates with the sizes as weights is
the crude rate of the population: its total number of events over its total size. With the sizes
$S_i$ of a standard population as weights, $(\sum_i S_i T_i) / \sum_i S_i$ is the rate of $T$
directly standardized to that standard, the crude rate of a population with the standard's
composition and the rates $T_i$. Both are $0$ when the total of the weights is $0$.
