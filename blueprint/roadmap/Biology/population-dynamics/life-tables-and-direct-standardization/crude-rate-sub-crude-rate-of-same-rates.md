# With common category rates, the crude-rate gap is a composition effect

Let $\iota$ be a finite set of categories, $N_i$ and $n_i$ the real sizes of two populations, with
[population shares](population-share.md) $S_i = N_i / \sum_j N_j$ and $s_i = n_i / \sum_j n_j$, and
let both populations have the same real rates $T_i$. Then the difference of their
[crude rates](../../statistical-genetics/mendelian-randomization/weighted-mean.md) is
$c(n, T) - c(N, T) = \sum_i T_i (s_i - S_i)$, and this sum also equals the difference of the
[directly standardized rates](directly-standardized-rate-eq-crude-rate.md) of $T$ under the
standards $n$ and $N$. It is the composition effect of the
[rate and composition decomposition](crude-rate-sub-crude-rate.md) when the two sets of rates
are equal, the rate effect then being $0$. The identities hold for all real sizes: when the total
size of a population is $0$, its shares are all $0$ by the convention $x / 0 = 0$, and so are its
crude rate and the rate standardized to it.
