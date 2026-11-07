# Cui–Gu $p$-dissection of $f_1$

Let $p \ge 5$ be a prime, let $s = (p - 1)/6$ if
$p \equiv 1 \pmod 6$ and $s = (-p - 1)/6$ otherwise, and let $q$ be a complex number with
$|q| < 1$. Write $f_k = (q^k; q^k)_\infty = \prod_{m \ge 1} (1 - q^{km})$, let
$f(a, b) = \sum_{n \in \mathbb{Z}} a^{n(n+1)/2} b^{n(n-1)/2}$ be Ramanujan's theta function, and
let $K$ be the set of integers $k$ with $(1 - p)/2 \le k \le (p - 1)/2$ and $k \ne s$. Then

$$
f_1 = \sum_{k \in K} (-1)^k q^{k(3k+1)/2}
f\bigl(-q^{(3p^2 + (6k+1)p)/2}, -q^{(3p^2 - (6k+1)p)/2}\bigr) +
(-1)^s q^{(p^2-1)/24} f_{p^2}.
$$

All the divisions are exact and all the exponents of $q$ are nonnegative integers.

## Sources

- Mohammed L. Nadji and Moussa Ahmia, *Congruences for l-Regular Tripartitions for l in {2,3}*, INTEGERS 24 (2024), Article A86, Lemma 5, eq. (8) (`integers-2024-A86-lem-5`), quoting S. Cui and N. Gu, *Arithmetic Properties of ℓ-Regular Partitions*, Adv. Appl. Math. 51 (2013), 507–523, Theorem 2.2. The same identity is Nayaka, Dharmendra and Mahesh Kumar, *Divisibility Properties for Overcubic Partition Triples*, INTEGERS 24 (2024), Article A80, Lemma 4, eq. (43) (`integers-2024-A80-lem-4`).
