# Josephus survivor via iteration from zero

Let $k \ge 2$ and $n \ge 1$ be natural
numbers, let $h_k(x) = x + \lfloor x/(k-1) \rfloor + 1$ for natural numbers $x$, and write
$h_k^p$ for the $p$-th iterate of $h_k$. Then there is a natural number $p \ge 1$ with
$h_k^{p-1}(0) < n(k-1) \le h_k^p(0)$ and $J_k(n) = nk - h_k^p(0)$, where $J_k$ is the Josephus
function for elimination step $k$.

## Sources

- Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*, INTEGERS 24 (2024), Article G5, Theorem 3.
