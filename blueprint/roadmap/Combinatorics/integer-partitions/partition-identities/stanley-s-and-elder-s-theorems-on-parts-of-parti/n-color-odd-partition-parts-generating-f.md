# Generating function for the number of parts in n-color partitions into odd parts

For
$i \ge 0$ let $Q(O, i)$ be the total number of parts, counted with multiplicity, over the
$n$-color partitions of $i$ into odd parts (every part has odd size). Then in the ring
$\mathbb{Q}[[q]]$ of formal power series, with infinite sums and products taken coefficientwise,

$$
\sum_{m \ge 0} \frac{(2m+1)\,q^{2m+1}}{1 - q^{2m+1}} =
\prod_{m \ge 0} (1 - q^{2m+1})^{2m+1} \sum_{i \ge 0} Q(O, i)\, q^i.
$$

## Sources

- Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*, INTEGERS 25 (2025), Article A94, Theorem 9.
