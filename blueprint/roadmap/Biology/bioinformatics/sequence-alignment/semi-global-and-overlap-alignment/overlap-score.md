# Overlap alignment score

The overlap score of $x$ and $y$ is $\mathrm{Ov}(x, y) = \max\bigl(0, \max_{(x', y')} \mathrm{NW}(x', y')\bigr)$, the maximum over the [overlap pairs](overlap-pairs.md), where $\mathrm{NW}$ is the [Needleman–Wunsch score](../pairwise-sequence-alignment/nw-score.md).
