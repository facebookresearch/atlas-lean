# Sampled-suffix-array locate is correct

Let $t = t_0 \cdots t_{n-1}$ be a text over a linearly ordered alphabet, let $SA$ be the suffix
array of $t$ followed by a sentinel smaller than every letter, and let a sampling assign to some
rows $r$ a stored value $s(r)$. Assume that every stored value of a row $r \le n$ is correct,
$s(r) = SA[r]$, and that every row $r \le n$ with $SA[r] = 0$ is sampled. Then for every row
$r \le n$, sampled locate on the Burrows–Wheeler transform of $t$ returns $SA[r]$.
