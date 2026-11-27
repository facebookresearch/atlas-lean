# Expected comparisons of quicksort on a random permutation

Let $\ell$ be a list without
repeated entries over a linear order. The expected number of comparisons made by quicksort on the
list obtained by rearranging the entries of $\ell$ by a uniformly random permutation of their
positions, computed in the extended nonnegative reals $[0, \infty]$, equals

$$\sum_{a < b} \frac{2}{d(a, b) + 2},$$

where the sum runs over pairs of entries $a < b$ of $\ell$ and $d(a, b)$ is the number of entries
of $\ell$ strictly between $a$ and $b$ (CLRS Section 7.4).
