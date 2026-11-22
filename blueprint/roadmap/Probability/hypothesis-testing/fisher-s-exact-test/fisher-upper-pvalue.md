# One-sided Fisher exact p-value

For a $2 \times 2$ table with group sizes $n_1$ and $n_2$ and success margin $t \le n_1 + n_2$, the upper
Fisher exact p-value at a natural number $x$ is the probability of a count at least $x$ under the
hypergeometric law with population $n_1 + n_2$, $n_1$ marked items and $t$ draws; it is $0$ when $x > t$.
It applies to any natural-valued statistic $X$, at its observed value $X(\omega)$, whether or not that
value fits the table's margins; the test uses the observed count of successes in the first group.
