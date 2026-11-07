# Spans of the odd and even entries of a perfect cover

Let $m$, $n$ and $k$ be natural
numbers with $k + 1 \le m + n$, and let $s = (s_1, \dots, s_{m+n})$, $s_i = (x_i, y_i)$, be a
family in $(\mathbb{Z}_2)^m \oplus \mathbb{Z}_{2^n}$ that is a perfect $1$-cover: every element of
the group is the sum of the $s_i$ over exactly one set of indices. Suppose that $y_i$, read as an
integer in $\{0, \dots, 2^n - 1\}$, is odd exactly when $i \le k + 1$. Let $U$ be the
$\mathbb{Z}_2$-span of $x_1 + x_2, \dots, x_1 + x_{k+1}$ and $V$ the $\mathbb{Z}_2$-span of
$x_{k+2}, \dots, x_{m+n}$ in $(\mathbb{Z}_2)^m$. Then $\dim U = k$, $\dim V = m - k$,
$U \cap V = 0$ and $U + V = (\mathbb{Z}_2)^m$.

## Sources

- John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Lemma 23 (`jis-2025-25.7.8-lem-23`). Indices are `0`-based (`i < k + 1` are the odd ones, and `k + 1 ≤ m + n` makes `y_1, …, y_{k+1}` exist); the perfect cover is an indexed family (perfect covers have distinct entries); `(ℤ₂)^m = U ⊕ V` is stated as `U ⊔ V = ⊤`.
