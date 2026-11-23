# A split of the second sequence scores at most the Needleman–Wunsch optimum

For all sequences $x, y$ and natural numbers $m, k$,

$$\mathrm{NW}(x_{<k}, y_{<m}) + \mathrm{NW}(x_{\ge k}, y_{\ge m}) \le \mathrm{NW}(x, y),$$

where $x_{<k}$ is the prefix of the first $k$ letters of $x$ (all of $x$ if $k > |x|$), $x_{\ge k}$ the rest, and $\mathrm{NW}$ the [Needleman–Wunsch score](../pairwise-sequence-alignment/nw-score.md).
