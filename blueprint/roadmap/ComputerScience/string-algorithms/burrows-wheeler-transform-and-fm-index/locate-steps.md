# Number of LF steps taken by sampled locate

Let $L$ be a list over a linearly ordered alphabet with a least letter $\bot$ adjoined, with
LF-mapping $\mathrm{LF}$, and let a sampling assign stored values to some rows. The number of LF
steps of the $k$-step locate from row $r$ is $0$ when $k = 0$; with $k + 1$ steps it is $0$ if row
$r$ is sampled and otherwise $1$ plus the number of LF steps of the $k$-step locate from row
$\mathrm{LF}(r)$.
