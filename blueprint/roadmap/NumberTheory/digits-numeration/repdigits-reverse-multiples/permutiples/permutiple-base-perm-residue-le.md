# Holt's residue condition for rearranged permutiples

Let $n \ge 1$ and $b \ge 2$ be
natural numbers, let $d_0, \dots, d_k$ be natural numbers, and write $(e_k, \dots, e_0)_b$
for the base-$b$ numeral $\sum_{j=0}^{k} e_j b^j$. Let $\sigma$, $\pi$ and $\tau$ be
permutations of $\{0, \dots, k\}$. If $(d_k, \dots, d_0)_b$ is an $(n, b, \sigma)$-permutiple
and $(d_{\pi(k)}, \dots, d_{\pi(0)})_b$ is an $(n, b, \tau)$-permutiple, then for every
$0 \le j \le k$

$$\lambda\bigl(d_j + (b - n)\, d_{\pi(\tau(\pi^{-1}(j)))}\bigr) \le n - 1,$$

where $\lambda(x)$ is the least non-negative residue of the integer $x$ modulo $b$ (the
difference $b - n$ is taken in the integers and may be negative).

The hypothesis $n \ge 1$ is needed: for $n = 0$ the only permutiples have all digits zero
and the bound would read $0 \le -1$.

## Sources

- B. V. Holt, *A Method for Finding All Permutiples with a Fixed Set of Digits from a Single Known Example*, INTEGERS 24 (2024), Article A88, Theorem 3 (`integers-2024-A88-thm-3`).
