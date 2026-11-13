# Counting values of the variation against the invariant measure

Let $\mathbb{X}$ be the
set of Zeckendorf-adic integers, $T$ the Zeckendorf odometer, and $\mathbb{P}$ a $T$-invariant
probability measure on binary sequences with $\mathbb{P}(\mathbb{X}^c) = 0$. Let $s(n)$ be the
number of terms in the Zeckendorf representation of $n \in \mathbb{N}$, let $\iota(n)$ be the
Zeckendorf digit sequence of $n$, let $\Delta^{(r)}$ and $\Delta_k^{(r)}$ be the variation and the
truncated variation on binary sequences, and let $\varphi$ be the golden ratio. Then for all
integers $r \ge 1$, $N \ge 1$, $k \ge 2$ and $d, d' \in \mathbb{Z}$,

$$\frac{1}{N}\,\#\{n < N : s(n + r) - s(n) = d,\ \Delta_k^{(r)}(\iota(n)) = d'\}
\le r\varphi^3\,\mathbb{P}(\Delta^{(r)} = d,\ \Delta_k^{(r)} = d')$$

and

$$\frac{1}{N}\,\#\{n < N : s(n + r) - s(n) = d\} \le r\varphi^3\,\mathbb{P}(\Delta^{(r)} = d).$$

## Sources

- Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation: An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27 (2024), Article 24.3.2, Lemma 26 (`jis-2024-24.3.2-lem-26`).
