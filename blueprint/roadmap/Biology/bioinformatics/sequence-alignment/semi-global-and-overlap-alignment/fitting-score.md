# Fitting score

The fitting score of $x$ in $y$ is $\mathrm{Fit}(x, y) = \max_{l} \mathrm{NW}(x, l)$, the maximum over the [infixes](infixes.md) $l$ of $y$ (the empty infix included), where $\mathrm{NW}$ is the [Needleman–Wunsch score](../pairwise-sequence-alignment/nw-score.md). Unlike the [overlap score](overlap-score.md), it is not floored at $0$ and can be negative.
