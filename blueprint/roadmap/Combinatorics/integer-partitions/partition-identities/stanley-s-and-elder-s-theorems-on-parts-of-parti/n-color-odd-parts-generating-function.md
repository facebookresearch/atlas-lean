# Generating function for the number of odd parts in n-color partitions

For $i \ge 0$ let
$A_o(i)$ be the total number of odd parts (parts of odd size, counted with multiplicity) over the
$n$-color partitions of $i$. Then in the ring $\mathbb{Q}[[q]]$ of formal power series, with
infinite sums and products taken coefficientwise,

$$
\sum_{m \ge 0} \frac{(2m+1)\,q^{2m+1}}{1 - q^{2m+1}} =
\prod_{m \ge 1} (1 - q^m)^m \sum_{i \ge 0} A_o(i)\, q^i.
$$

## Sources

- Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*, INTEGERS 25 (2025), Article A94, Theorem 5 (`integers-2025-A94-thm-5`).
