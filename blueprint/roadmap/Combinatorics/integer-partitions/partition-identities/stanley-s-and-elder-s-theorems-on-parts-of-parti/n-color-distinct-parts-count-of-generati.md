# Generating function for parts of a given size in distinct $n$-color partitions

Call an
$n$-color partition distinct when no colored part occurs more than once. For a natural number
$j$, let $Q(D, j, m)$ be the total number of parts of size $j$ (of any color) over the distinct
$n$-color partitions of $m$, and let $C(D, m)$ be the number of distinct $n$-color partitions of
$m$. Then, as formal power series in $q$ over $\mathbb{Q}$,

$$\sum_{m \ge 0} Q(D, j, m) \, q^m = \frac{j q^j}{1 + q^j} \sum_{m \ge 0} C(D, m) \, q^m.$$

The paper assumes $j \ge 1$; for $j = 0$ both sides vanish.

## Sources

- Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*, INTEGERS 25 (2025), Article A94, Theorem 11.
