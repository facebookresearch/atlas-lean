# The Fisher exact p-value as a hypergeometric tail sum

For a $2 \times 2$ table with group sizes $n_1$ and $n_2$ and success margin $t \le n_1 + n_2$, the upper
Fisher exact p-value of an observed count $x$ of successes in the first group is
$$\sum_{j = x}^{t} \frac{\binom{n_1}{j}\binom{n_2}{t - j}}{\binom{n_1 + n_2}{t}}.$$
