# Population share of a category as its size over the total

For a finite set $\iota$ of categories (for example age groups) and real sizes $N_i$, the share of
category $i$ is $N_i / \sum_{j \in \iota} N_j$. With the convention $x / 0 = 0$, every share is $0$
when the total $\sum_j N_j$ is $0$, for example when every size is $0$. The intended domain is a
[valid population](is-valid-population.md), with nonnegative sizes and a positive total: the shares
then lie in $[0, 1]$ ([bounds](population-share-mem-icc.md)) and sum to $1$
([sum](sum-population-share.md)), and they describe the composition of the population. For signed
sizes with a nonzero total the shares still sum to $1$ but can be negative or greater than $1$.

Source: P. Das Gupta, *Standardization and Decomposition of Rates: A User's Manual*, U.S. Bureau of
the Census (1993), eq. (5.2).
