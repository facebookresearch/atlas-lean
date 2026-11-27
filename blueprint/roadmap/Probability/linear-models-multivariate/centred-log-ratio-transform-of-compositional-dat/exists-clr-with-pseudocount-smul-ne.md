# A fixed pseudocount can break scale invariance

There are counts $n = (n_1, n_2)$ on two parts, with $n_1, n_2 \ge 0$, such that, with the
pseudocount $1$, doubling the counts changes the [CLR transform](clr.md) of the
[pseudocount composition](with-pseudocount.md):

$$\operatorname{clr}(2n + 1) \ne \operatorname{clr}(n + 1),$$

where $n + 1 = (n_1 + 1, n_2 + 1)$ and $2n + 1 = (2n_1 + 1, 2n_2 + 1)$. For example,
$n = (0, 1)$ gives the compositions $(1, 2)$ and $(1, 3)$, whose CLR transforms are
$(-\frac12 \log 2, \frac12 \log 2)$ and $(-\frac12 \log 3, \frac12 \log 3)$.
