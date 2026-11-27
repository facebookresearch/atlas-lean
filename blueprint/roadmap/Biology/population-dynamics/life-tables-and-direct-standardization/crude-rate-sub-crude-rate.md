# Crude-rate difference as a rate effect plus a composition effect

Let $\iota$ be a finite set of categories, and consider two populations, one with real sizes $N_i$
and rates $T_i$, the other with real sizes $n_i$ and rates $t_i$. Write $S_i = N_i / \sum_j N_j$ and
$s_i = n_i / \sum_j n_j$ for their [population shares](population-share.md), $c(N, T)$ and $c(n, t)$
for their [crude rates](../../statistical-genetics/mendelian-randomization/weighted-mean.md), $\bar s_i = (s_i + S_i) / 2$ for the average shares and
$\bar r_i = (t_i + T_i) / 2$ for the average rates. Then $c(n, t) - c(N, T) = R + C$, where
$R = \sum_i \bar s_i t_i - \sum_i \bar s_i T_i$ is the rate effect, the two sets of rates compared
at the average shares, and $C = \sum_i \bar r_i s_i - \sum_i \bar r_i S_i$ is the composition
effect, the two sets of shares compared at the average rates.

This is Kitagawa's decomposition, with the average shares and the average rates of the two
populations as standards. It holds for all real sizes and rates: when the total size of a population
is $0$, its shares are all $0$ by the convention $x / 0 = 0$, its crude rate is $0$, and the
identity still holds.

Source: P. Das Gupta, *Standardization and Decomposition of Rates: A User's Manual*, U.S. Bureau of
the Census (1993), eq. (5.3) for the rate effect and eq. (5.4) for the composition effect, after
E. M. Kitagawa (1955).
