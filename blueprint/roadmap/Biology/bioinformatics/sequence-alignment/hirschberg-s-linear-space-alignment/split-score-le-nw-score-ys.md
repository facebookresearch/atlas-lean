# A split of the second sequence scores at most the Needleman–Wunsch optimum

Let
$\sigma$ be an integer-valued substitution score on an alphabet, let $g$ be an integer gap
score, and write $\mathrm{NW}(x, y)$ for the optimal Needleman–Wunsch global alignment score
of sequences $x$ and $y$ under $\sigma$ and $g$. For sequences $x$, $y$ and natural numbers
$k$, $m$, let $x_{\lt k}$ be the first $k$ letters of $x$ (all of $x$ if $k$ is at least its
length) and $x_{\ge k}$ the remaining letters, and define $y_{\lt m}$ and $y_{\ge m}$ likewise.
Then $\mathrm{NW}(x_{\lt k}, y_{\lt m}) + \mathrm{NW}(x_{\ge k}, y_{\ge m}) \le \mathrm{NW}(x, y)$.

The bound holds because optimal alignments of the two halves concatenate to an alignment of
$x$ and $y$.
