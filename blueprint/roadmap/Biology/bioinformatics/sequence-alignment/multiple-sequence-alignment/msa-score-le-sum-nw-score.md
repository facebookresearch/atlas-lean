# The sum-of-pairs score is bounded by the pairwise optima

If $A$ is a [valid multiple alignment](is-msalignment.md) of $s_0, \dots, s_{k-1}$, then its [sum-of-pairs score](msa-score.md) is at most $\sum_{i < j} \mathrm{NW}(s_i, s_j)$, where $\mathrm{NW}$ is the [Needleman–Wunsch score](../pairwise-sequence-alignment/nw-score.md).
