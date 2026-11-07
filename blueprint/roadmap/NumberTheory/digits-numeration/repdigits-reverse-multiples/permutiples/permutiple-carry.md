# Carries of a permutiple multiplication

Let $n$, $b$ and $d_0, \dots, d_k$ be
natural numbers and let $\sigma$ be a permutation of $\{0, \dots, k\}$. The carries of the
single-digit multiplication $n \cdot (d_{\sigma(k)}, \dots, d_{\sigma(0)})_b$, where
$(e_k, \dots, e_0)_b$ denotes the base-$b$ numeral $\sum_{j=0}^{k} e_j b^j$, are the
natural numbers $c_0, c_1, c_2, \dots$ defined by $c_0 = 0$,
$c_{j+1} = \lfloor (n d_{\sigma(j)} + c_j) / b \rfloor$ for $0 \le j \le k$, and
$c_{j+1} = 0$ for $j > k$. Division by $b = 0$ is taken to give $0$.

## Sources

- B. V. Holt, *A Method for Finding All Permutiples with a Fixed Set of Digits from a Single Known Example*, INTEGERS 24 (2024), Article A88, Section 2.
