# Generating functions for the parts of distinct $n$-color partitions

Call an $n$-color
partition distinct when no colored part occurs more than once, and let $C_o(D, m)$ (resp.
$C_e(D, m)$) be the total number of parts over the distinct $n$-color partitions of $m$ with an
odd (resp. even) number of parts. Then, as formal power series in $q$ over $\mathbb{Q}$, with
infinite sums and products taken coefficientwise, both

$$
\sum_{m \ge 1} \frac{m q^m}{1 + q^m} =
\Big(\prod_{m \ge 1} (1 + q^m)^m\Big)^{-1} \sum_{m \ge 0} \big(C_o(D, m) + C_e(D, m)\big) q^m
$$

and

$$
\sum_{m \ge 1} \frac{m q^m}{1 - q^m} =
\Big(\prod_{m \ge 1} (1 - q^m)^m\Big)^{-1} \sum_{m \ge 0} \big(C_o(D, m) - C_e(D, m)\big) q^m
$$

hold.

## Sources

- Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*, INTEGERS 25 (2025), Article A94, Theorem 8.
