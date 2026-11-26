# The Smith–Waterman score

The Smith–Waterman score of $x$ and $y$ is $\mathrm{SW}(x, y) = \max\bigl(0, \max_{(p, q)} H(p, q)\bigr)$, the maximum over the [prefix pairs](prefix-pairs.md) of the [terminal cell](sw-cell-score.md). For $g \le 0$ it is the [local score](local-score.md); for $g > 0$ it can be smaller.
