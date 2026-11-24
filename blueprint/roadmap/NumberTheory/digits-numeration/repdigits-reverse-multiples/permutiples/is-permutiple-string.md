# Permutiple strings

Let $n$ and $b$ be natural numbers, and for natural numbers
$a_0, \dots, a_k$ write $(a_k, \dots, a_0)_b = \sum_{j=0}^{k} a_j b^j$. A string $s$ of inputs
(pairs of natural numbers) is an $(n, b)$-permutiple string when it belongs to the language $L$ of
the $(n, b)$-Hoey-Sloane machine and there are a natural number $k$, natural numbers
$d_0, \dots, d_k$ and a permutation $\sigma$ of $\{0, \dots, k\}$ such that $(d_k, \dots, d_0)_b$
is an $(n, b, \sigma)$-permutiple, that is, every $d_j$ is less than $b$ and
$(d_k, \dots, d_0)_b = n (d_{\sigma(k)}, \dots, d_{\sigma(0)})_b$, and
$s = (d_0, d_{\sigma(0)})(d_1, d_{\sigma(1)}) \cdots (d_k, d_{\sigma(k)})$.

## Sources

- Benjamin V. Holt, *A Multigraph Characterization of Permutiple Strings*, INTEGERS 25 (2025), Article A111, Section 2.3.
