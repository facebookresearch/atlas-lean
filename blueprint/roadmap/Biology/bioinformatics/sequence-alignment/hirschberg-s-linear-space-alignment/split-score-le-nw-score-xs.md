# A split of the first sequence scores at most the Needleman–Wunsch optimum

Let
$\sigma$ be an integer-valued substitution score on an alphabet, let $g$ be an integer gap
score, and write $\mathrm{NW}(x, y)$ for the optimal Needleman–Wunsch global alignment score
of sequences $x$ and $y$ under $\sigma$ and $g$. For sequences $x$, $y$ and natural numbers
$m$, $k$, let $x_{\lt m}$ be the first $m$ letters of $x$ (all of $x$ if $m$ is at least its
length) and $x_{\ge m}$ the remaining letters, and define $y_{\lt k}$ and $y_{\ge k}$ likewise.
Then $\mathrm{NW}(x_{\lt m}, y_{\lt k}) + \mathrm{NW}(x_{\ge m}, y_{\ge k}) \le \mathrm{NW}(x, y)$.
