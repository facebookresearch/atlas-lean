# Crude rate as the share-weighted sum of category rates

For a finite set $\iota$ of categories and arbitrary real sizes $N_i$ and rates $T_i$, the
[crude rate](../../statistical-genetics/mendelian-randomization/weighted-mean.md) equals $\sum_i s_i T_i$, where $s_i = N_i / \sum_j N_j$ is the
[population share](population-share.md) of category $i$. The identity holds for all real sizes: when
the total size is $0$, every share is $0$ by the convention $x / 0 = 0$, and both sides are $0$.

Source: P. Das Gupta, *Standardization and Decomposition of Rates: A User's Manual*, U.S. Bureau of
the Census (1993), eqs. (5.1)–(5.2).
