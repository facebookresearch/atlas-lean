# Proper $L^*$-blocks

Let $L$ be a list of natural numbers. Lean's zero-based interval
$[s, k]$ corresponds to Chang's $[s+1, k+1]$. Let $B$ be the maximal block starting at Lean index
$s$, so $B_i$ is the entry of Chang's $\bar\beta^{s+1}$ at index $i+1$.
A function $\zeta : \mathbb N \to \mathbb N$ is a proper $L^*$-block with support interval $[s, k]$
when $s \le k$, $\zeta_i = B_i$ for all $i < k$, $\zeta_k < B_k$, and $\zeta_i = 0$ for all
$i > k$. Since $B$ vanishes below $s$, so does $\zeta$.

## Sources

- Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25, Section 2 (arXiv:2308.12872v1, Section 2.3).
