# Restricted-growth word generating function

Fix $k \ge 0$. A word $u_1 u_2 \cdots u_n$
in the letters $1, \dots, k$ is a restricted-growth word if for every $i$, either $u_i = 1$ or
$u_i \le u_j + 1$ for some $j < i$ (so a nonempty such word begins with $1$). For
$d = (d_1, \dots, d_k) \in \mathbb{N}^k$, let $r(d)$ be the number of restricted-growth words in
which each letter $a$ occurs exactly $d_a + 1$ times. Then, in the ring of formal power series
in $x_1, \dots, x_k$ over $\mathbb{Q}$,

$$\sum_{d} r(d)\, x_1^{d_1} \cdots x_k^{d_k} = \prod_{j=1}^{k} (1 - x_1 - \cdots - x_j)^{-1}.$$

Proof: Decompose restricted-growth words by their first letter to obtain a coefficient
recurrence, lift it to multivariate power series, and iterate power-series inverse
cancellation. The combinatorial route follows Ehrenborg, Hedmark, and Hettle, Theorem 1.

## Sources

- Richard Ehrenborg, Dustin Hedmark, and Cyrus Hettle, "A Restricted Growth Word Approach to Partitions with Odd/Even Size Blocks," Journal of Integer Sequences 20 (2017), Article 17.5.5, Theorem 1, lines 190-200, <https://cs.uwaterloo.ca/journals/JIS/VOL20/Ehrenborg/ehren4.tex>.
