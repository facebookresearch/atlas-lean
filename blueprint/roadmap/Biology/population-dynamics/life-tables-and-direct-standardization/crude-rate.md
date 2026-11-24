# Crude rate as the size-weighted sum of rates over the total size

For a finite set $\iota$ of categories, real sizes $N_i$ and real rates $T_i$, the crude rate is the
centre of mass of the rates $T_i$ with masses $N_i$, $(\sum_i N_i)^{-1} \sum_i N_i T_i$, which
equals $(\sum_i N_i T_i) / \sum_i N_i$
([total events over total size](crude-rate-eq-sum-mul-div.md)). With the convention $0^{-1} = 0$ it
is $0$ when the total size $\sum_i N_i$ is $0$, whatever the rates.

For a [valid population](is-valid-population.md), with nonnegative sizes and a positive total, the
crude rate is a weighted average of the category rates, with the
[population shares](population-share.md) $N_i / \sum_j N_j$ as weights, and it lies between the
smallest and the largest rate ([bounds](crude-rate-mem-icc.md)). For signed sizes with a nonzero
total the weights still sum to $1$ but can be negative, and the crude rate can then lie outside the
range of the rates.

Source: P. Das Gupta, *Standardization and Decomposition of Rates: A User's Manual*, U.S. Bureau of
the Census (1993), eq. (5.1).
