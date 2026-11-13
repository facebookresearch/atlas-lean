# The full-match shift is the least period of the pattern

Let $p = p_0 \cdots p_{m-1}$
be a nonempty pattern over the alphabet $\{0, \dots, \sigma - 1\}$ and let $G$ be the good-suffix
table computed by the Boyer–Moore preprocessing of $p$. Then $1 \le G_0 \le m$,
$p_{t - G_0} = p_t$ for every $t < m$ with $G_0 \le t$, and $G_0 \le e$ for every positive
integer $e$ such that $p_{t - e} = p_t$ for every $t < m$ with $e \le t$. That is, $G_0$ is the
least positive period of $p$.

So after a full match the matcher may shift by $G_0$ without discarding overlapping
occurrences.
