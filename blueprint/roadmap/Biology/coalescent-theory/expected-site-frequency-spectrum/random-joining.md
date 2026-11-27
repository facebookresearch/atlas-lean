# Random-joining law on block-size lists

For a natural number $m$, a list $b$ of block sizes and a list $\mathbf{p}$ of block-size lists, the number $R_m(b, \mathbf{p})$ is defined by recursion on $m$:

- $R_0(b, \mathbf{p}) = 1$ if $\mathbf{p} = (b)$ and $0$ otherwise;
- if $b$ has fewer than two entries, $R_{m+1}(b, \mathbf{p}) = 1$ if $\mathbf{p} = (b)$ and $0$ otherwise;
- otherwise $R_{m+1}(b, \mathbf{p}) = 0$ unless $\mathbf{p}$ starts with $b$, and if $\mathbf{p} = (b, \mathbf{p}')$, then $R_{m+1}(b, \mathbf{p})$ is the average of $R_m(b', \mathbf{p}')$ over the lists $b'$ obtained from $b$ by [merging the blocks](merge-blocks.md) at positions $i < j$, over all such pairs of positions.

So $R_m(b, \mathbf{p})$ is the probability that $m$ steps of random joining started from $b$ visit the sequence of lists $\mathbf{p}$, starting with $b$ itself: each step merges a pair of blocks chosen uniformly among all pairs, and the process stops once fewer than two blocks remain.
