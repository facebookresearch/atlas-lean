# Generating function for parts in a residue class over n-color partitions

Let $r$ and
$k$ be natural numbers with $0 < k < r$, and for $i \ge 0$ let $C(k \bmod r, i)$ be the total
number of parts of size congruent to $k$ modulo $r$, counted with multiplicity, over the
$n$-color partitions of $i$. Then in the ring $\mathbb{Q}[[q]]$ of formal power series, with
infinite sums and products taken coefficientwise,

$$
\sum_{m \ge 0} \frac{(rm+k)\,q^{rm+k}}{1 - q^{rm+k}} =
\prod_{m \ge 1} (1 - q^m)^m \sum_{i \ge 0} C(k \bmod r, i)\, q^i.
$$

## Sources

- Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*, INTEGERS 25 (2025), Article A94, Theorem 7.
