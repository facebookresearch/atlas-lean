# Josephus elimination positions as Maximum Nim Grundy numbers

Let $k \ge 2$ and
$1 \le m \le n$. Write $o_n(m)$ for the position, counting from $1$, at which $m$ appears in the
Josephus elimination order of the circle $1, \dots, n$ in which every $k$-th person is removed
and the survivor is listed last, and write $G$ for the Grundy number of Maximum Nim with rule
function $f(y) = \lfloor y/k \rfloor$. Then $n - o_n(m) = G(nk - m)$.

## Sources

- Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*, INTEGERS 24 (2024), Article G5, Theorem 2 (`integers-2024-G5-thm-2`).
