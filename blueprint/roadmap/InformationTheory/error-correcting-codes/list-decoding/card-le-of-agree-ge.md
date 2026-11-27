# Reed–Solomon codes are list decodable up to the Johnson radius

Let $\alpha_1, \dots, \alpha_n \in F$ be distinct, $1 \le k \le n$, $y \in F^n$, and $t \le n$
with $t^2 > n (k - 1)$. Every finite set of polynomials of degree less than $k$, each agreeing
with $y$ in at least $t$ positions, has at most $n (n - k + 1)$ elements.

So [Reed–Solomon codes](../reed-solomon-codes/README.md) of rate $R = k/n$ are list decodable with
polynomial list size from any fraction of errors below $1 - \sqrt{R}$ (agreement
$t > \sqrt{n(k-1)}$). This is the Johnson bound (Theorem 7.3.3 of Guruswami, Rudra and Sudan,
strict case) applied to the MDS Reed–Solomon codes (their Theorem 5.2.4): the list-size guarantee
behind their Theorem 12.2.12. The [Guruswami–Sudan decoder](exists-interpolant-dvd.md) is
correct for any admissible parameters $D, r$, and a suitable choice of $D, r$ reaches this radius in
polynomial time.

## Informally uses

- [Johnson bound, list size $n d$](card-le-mul-of-johnson.md): applied with $d = n - k + 1$ and $e = n - t$, so that $n(n - d) = n(k-1) < t^2$.
- [Nonzero Reed-Solomon codewords are heavy](../reed-solomon-codes/le-hamming-norm-encode.md): distinct codewords are at distance at least $n - k + 1$ (the MDS property).

## Sources

- V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory*, draft of August 26, 2025, Theorems 5.2.4 and 7.3.3 (and Theorem 12.2.12 for context).
