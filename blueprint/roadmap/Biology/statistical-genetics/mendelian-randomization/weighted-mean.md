# Weighted mean

For a finite set $\iota$ and real vectors $v, a \in \mathbb{R}^\iota$, the weighted mean of $a$ with weights $v$ is

$$\bar a_v = \frac{\sum_j v_j a_j}{\sum_j v_j},$$

with the convention $x/0 = 0$.

In demography, with real category sizes $N_i$ and rates $T_i$ indexed by $\iota$ (for example age
groups), the weighted mean $(\sum_i N_i T_i) / \sum_i N_i$ of the rates with the sizes as weights is
the crude rate of the population: its total number of events over its total size. With the sizes
$S_i$ of a standard population as weights, $(\sum_i S_i T_i) / \sum_i S_i$ is the rate of $T$
directly standardized to that standard, the crude rate of a population with the standard's
composition and the rates $T_i$. The standard need not be normalised: its sizes are divided by
their total, and when they already sum to $1$ the rate is $\sum_i S_i T_i$. Both rates are $0$ when
the total of the weights is $0$.

For a
[valid population](../../population-dynamics/life-tables-and-direct-standardization/is-valid-population.md)
or standard, with nonnegative sizes and a positive total, the crude or standardized rate is an
average of the category rates and lies between the smallest and the largest of them
([bounds](../../population-dynamics/life-tables-and-direct-standardization/crude-rate-mem-icc.md)).
With signed sizes it can lie outside that range: sizes $(2, -1)$ with rates $(0, 1)$ give $-1$.

Source for direct standardization: P. Das Gupta, *Standardization and Decomposition of Rates: A
User's Manual*, U.S. Bureau of the Census (1993), chapter 1.
