# Thorup's high independence of double tabulation

Let $\Sigma = [2^b]$, $c \ge 1$ and $d \ge 6c$. With probability $1 - o(|\Sigma|^{2 - \lfloor d / (2c) \rfloor})$ over the random first-stage function $h_0 : \Sigma^c \to \Sigma^d$, the double tabulation function $h_1 \circ h_0$ is $k$-wise independent over the choice of $h_1$ for $k = |\Sigma|^{1/(5c)}$. In particular, for keys of $c$ characters, double tabulation gives, with high probability, an $|\Sigma|^{\Omega(1/c)}$-wise independent family evaluated in $O(c + d)$ time from $O((c + d)|\Sigma|)$ space.

## Proof sketch

Thorup shows that with the stated probability $h_0$ is $k$-unique: every set of at most $k$ keys has a derived character that appears in exactly one of their derived keys. A simple tabulation function applied to a $k$-unique family of derived keys is $k$-wise independent, because the table entry of the unique character is an independent uniform mask for one key.

## Depends on

- [Double tabulation hashing](double-tabulation-hashing.md)
- [k-wise independent hash family](k-wise-independent-hash-family.md)

## Proof depends on

- [Finite k-wise independent families meet the k-wise contract](k-wise-families-meet-the-contract.md)

## Sources

- M. Thorup, "Simple Tabulation, Fast Expanders, Double Tabulation, and High Independence", Proceedings of the 54th IEEE Symposium on Foundations of Computer Science (FOCS), 2013; arXiv:1311.3121.
