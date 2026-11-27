# Substring complexity is at most the attractor size

For every string $T$, $\delta(T) \le \gamma(T)$. More precisely, if $\Gamma$ is a string attractor of $T$, then $d_k(T) \le k\,|\Gamma|$ for every $k \ge 1$.

## Proof sketch

Every distinct substring of length $k$ has an occurrence crossing some $p \in \Gamma$, so it equals $T[p - s .. p - s + k - 1]$ for some $p \in \Gamma$ and offset $s \in \{0, \dots, k-1\}$. There are at most $k|\Gamma|$ such pairs $(p, s)$, so $d_k(T) \le k|\Gamma|$, and dividing by $k$ and maximizing over $k$ gives the claim.

## Depends on

- [Substring complexity $\delta$](substring-complexity.md)
- [String attractors](string-attractor.md)

## Sources

- Tomasz Kociumaka, Gonzalo Navarro, Nicola Prezza, "Toward a Definitive Compressibility Measure for Repetitive Sequences", IEEE Transactions on Information Theory 69(4) (2023); LATIN (2020), arXiv:1910.02151.
- Anders Roy Christiansen, Mikko Berggren Ettienne, Tomasz Kociumaka, Gonzalo Navarro, Nicola Prezza, "Optimal-Time Dictionary-Compressed Indexes", ACM Transactions on Algorithms 17(1) (2021), arXiv:1811.12779.
