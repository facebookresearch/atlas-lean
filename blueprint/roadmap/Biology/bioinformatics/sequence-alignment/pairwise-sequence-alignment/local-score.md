# Local alignment score

The local score of $x$ and $y$ is $\mathrm{Loc}(x, y) = \max\bigl(0, \max_{(x', y')} \mathrm{NW}(x', y')\bigr)$, the maximum over the [infix pairs](infix-pairs.md), where $\mathrm{NW}$ is the [Needleman–Wunsch score](nw-score.md).
