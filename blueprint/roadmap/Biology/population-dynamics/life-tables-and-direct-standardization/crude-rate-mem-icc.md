# Crude rate of a valid population lies between the extreme rates

For a finite set $\iota$ of categories, a [valid population](is-valid-population.md) with real sizes
$N_i \ge 0$ and $\sum_j N_j > 0$, real rates $T_i$, and real numbers $a$ and $b$ with
$a \le T_i \le b$ for every category $i$, the [crude rate](../../statistical-genetics/mendelian-randomization/weighted-mean.md)
$(\sum_i N_i T_i) / \sum_i N_i$ lies in $[a, b]$. The bounds are required for every category,
including categories of size $0$. A valid population has at least one category, so taking for $a$
and $b$ the smallest and the largest rate shows that the crude rate lies between them.

The same holds for the directly standardized rate, the crude rate with the composition of a
standard population: for a valid standard $S$ and the same rates, $(\sum_i S_i T_i) / \sum_i S_i$
lies in $[a, b]$.
