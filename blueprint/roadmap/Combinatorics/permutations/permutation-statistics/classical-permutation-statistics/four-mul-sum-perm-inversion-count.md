# Total number of inversions over all permutations

For every $n$, the [inversion numbers](perm-inversion-count.md) of the $n!$ permutations of
$\{0, \dots, n-1\}$ add up to $n! \cdot n(n-1)/4$:

$$4 \sum_{\sigma \in S_n} \mathrm{inv}(\sigma) = n! \cdot n(n - 1).$$

Exchanging the order of summation, the total is the sum over the $\binom{n}{2}$
[pairs of positions](two-mul-card-filter-fst-lt-snd.md) of the number of permutations inverting the
pair, which is [$n!/2$ for each pair](two-mul-card-filter-lt.md). For $n = 3$ the inversion numbers
are $0, 1, 1, 2, 2, 3$, with sum $9$.

## Informally uses

- [Each pair of positions is inverted by exactly half of the permutations](two-mul-card-filter-lt.md):
  the count for one pair.
- [Number of pairs of positions](two-mul-card-filter-fst-lt-snd.md): the number of pairs.
