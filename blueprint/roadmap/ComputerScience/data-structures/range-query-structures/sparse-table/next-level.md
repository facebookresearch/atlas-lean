# Next level of a sparse table row

For a type with a minimum operation, an array
$(r_0, \dots, r_{n-1})$ and a natural number $k$, the next level is the array of length
$n - 2^k$ (empty when $2^k \ge n$) whose entry $i$ is $\min(r_i, r_{i + 2^k})$.

The construction of a sparse table computes each level once from the previous one this way.
