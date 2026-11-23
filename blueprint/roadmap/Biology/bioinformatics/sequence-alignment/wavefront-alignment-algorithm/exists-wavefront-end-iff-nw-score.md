# The wavefront algorithm computes the optimal alignment cost

For every natural number $s$: some $s' \le s$ has [wavefront offset](wavefront.md) $W(s', |y| - |x|) = |y|$ if and only if $-\mathrm{NW}(x, y) \le s$, where $\mathrm{NW}$ is the [Needleman–Wunsch score](../pairwise-sequence-alignment/nw-score.md) with the [substitution score](score.md) of the penalties and gap score $-g$.
