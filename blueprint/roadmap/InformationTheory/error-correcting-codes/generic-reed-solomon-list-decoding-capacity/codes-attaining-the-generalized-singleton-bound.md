# Codes attaining the generalized Singleton bound (LD-MDS codes)

A linear $[n, k]$ code $C$ over $\mathbb{F}$ is *$\mathrm{LD}$-$\mathrm{MDS}(L)$* (list-decoding MDS of order $L$, Roth's higher-order MDS notion) if it is $\big(\frac{L}{L+1}\cdot\frac{n-k}{n}, L\big)$-*average-radius* list decodable: for every $y \in \mathbb{F}^n$ and all $L + 1$ distinct codewords $c_0, \dots, c_L \in C$,

$$
\sum_{j=0}^{L} \mathrm{wt}(c_j - y) > L(n - k) .
$$

If $L+1$ distinct codewords lay in one Hamming ball of radius $\frac{L}{L+1}(n-k)$, their distances to its centre would sum to at most $L(n-k)$; so an $\mathrm{LD}$-$\mathrm{MDS}(L)$ code is also $\big(\frac{L}{L+1}\cdot\frac{n-k}{n}, L\big)$-list decodable in the ordinary sense, i.e. it attains the generalized Singleton bound for list size $L$. The ordinary-radius property is this consequence, not an equivalent definition; the duality theory of higher order MDS codes uses the average-radius condition. $C$ is $\mathrm{LD}$-$\mathrm{MDS}(\le L)$ if it is $\mathrm{LD}$-$\mathrm{MDS}(L')$ for all $1 \le L' \le L$; $\mathrm{LD}$-$\mathrm{MDS}(1)$ is the MDS property.

## Depends on

- [Generalized Singleton bound for list decoding (Shangguan-Tamo)](generalized-singleton-bound-for-list-decoding.md)
- [Linear code](../linear-codes/linear-code.md)

## Sources

- Ron M. Roth, "Higher-order MDS codes", IEEE Transactions on Information Theory 68(12) (2022).
- Joshua Brakensiek, Sivakanth Gopi, Visu Makam, "Generic Reed-Solomon codes achieve list-decoding capacity", STOC (2023), SIAM Journal on Computing (2024); arXiv:2206.05256, Definitions 1.2 and 1.9.
