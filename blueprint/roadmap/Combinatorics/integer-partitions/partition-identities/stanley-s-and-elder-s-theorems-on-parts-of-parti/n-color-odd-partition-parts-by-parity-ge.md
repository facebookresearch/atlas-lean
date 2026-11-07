# Parts of n-color partitions into odd parts, by parity of the number of parts

For
$i \ge 0$ let $U_o(i)$ (resp. $U_e(i)$) be the total number of parts, counted with multiplicity,
over the $n$-color partitions of $i$ into odd parts (every part has odd size) that have an odd
(resp. even) number of parts. Then in the ring $\mathbb{Q}[[q]]$ of formal power series, with
infinite sums and products taken coefficientwise,

$$
\sum_{m \ge 0} \frac{(2m+1)\,q^{2m+1}}{1 - q^{2m+1}} =
\prod_{m \ge 0} (1 - q^{2m+1})^{2m+1} \sum_{i \ge 0} \bigl(U_o(i) + U_e(i)\bigr) q^i
$$

and

$$
\sum_{m \ge 0} \frac{(2m+1)\,q^{2m+1}}{1 + q^{2m+1}} =
\prod_{m \ge 0} (1 + q^{2m+1})^{2m+1} \sum_{i \ge 0} \bigl(U_o(i) - U_e(i)\bigr) q^i.
$$

The paper's printed definition swaps the subscripts ($U_e$ for an odd number of parts); with it
the second identity fails at $q^1$: the left side has coefficient $1$, the right side
$U_o(1) - U_e(1) = 0 - 1 = -1$.

## Sources

- Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*, INTEGERS 25 (2025), Article A94, Theorem 12 (`integers-2025-A94-thm-12`).
