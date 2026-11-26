# Locality of the output of a `t`-round algorithm

Let `G` and `G'` be simple graphs on
the same finite set of `n` nodes, `ids` and `ids'` identifier assignments in `{1, …, n ^ c}`, and
`x`, `x'` inputs. If the identifiers and the inputs agree at every node at distance at most
`t n` from `v` in `G`, and the neighbours of every node at distance less than `t n` from `v` are
the same in `G` and `G'`, then the algorithm `A` run as a `t`-round algorithm outputs the same
at `v` in both networks.

## Sources

- N. Linial, *Locality in distributed graph algorithms*, SIAM Journal on Computing 21(1), 1992, 193–201, §2.
