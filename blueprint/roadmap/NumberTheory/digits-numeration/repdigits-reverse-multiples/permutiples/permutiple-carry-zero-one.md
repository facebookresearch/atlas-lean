# First two carries of a permutiple multiplication

Let $n$, $b$ and $d_0, \dots, d_k$
be natural numbers, let $\sigma$ be a permutation of $\{0, \dots, k\}$, and write
$(e_k, \dots, e_0)_b$ for the base-$b$ numeral $\sum_{j=0}^{k} e_j b^j$. The carries
$c_0, c_1, \dots$ of the single-digit multiplication
$n \cdot (d_{\sigma(k)}, \dots, d_{\sigma(0)})_b$, defined by $c_0 = 0$ and
$c_{j+1} = \lfloor (n d_{\sigma(j)} + c_j) / b \rfloor$ for $0 \le j \le k$, satisfy
$c_0 = 0$ and $c_1 = \lfloor n d_{\sigma(0)} / b \rfloor$, where division by $b = 0$ is
taken to give $0$.

## Sources

- B. V. Holt, *A Method for Finding All Permutiples with a Fixed Set of Digits from a Single Known Example*, INTEGERS 24 (2024), Article A88, Section 2.
