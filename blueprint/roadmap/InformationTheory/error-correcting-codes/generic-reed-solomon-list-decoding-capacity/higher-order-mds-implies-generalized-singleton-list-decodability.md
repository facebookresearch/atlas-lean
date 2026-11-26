# Higher order MDS codes attain the generalized Singleton bound

For every $L \ge 1$, an $\mathrm{MDS}(L+1)$ code $C$ of length $n$ and dimension $k$ is $\big(\frac{L}{L+1}\cdot\frac{n-k}{n}, L\big)$-list decodable, i.e. $\mathrm{LD}$-$\mathrm{MDS}(L)$. Conversely, codes that are $\mathrm{LD}$-$\mathrm{MDS}(\le L)$ are $\mathrm{MDS}(L+1)$ up to boundary cases in the sizes of the sets $A_i$, so the two notions of higher order MDS codes are nearly equivalent.

## Proof sketch

Suppose $L + 1$ distinct codewords $c_j = m_j G$ lie within distance $\frac{L}{L+1}(n-k)$ of a word $y$, with agreement sets $A_j$. The vectors $m_j - m_1$ then satisfy linear conditions expressing that they lie in the duals of intersections of the spaces $G_{A_j \cap A_{j'}}$. For a generic matrix $W$ a dimension count shows these conditions force all $m_j$ to coincide once $\sum_j |A_j|$ exceeds $L(k-1) + n$, which the radius guarantees. $\mathrm{MDS}(L+1)$ transfers exactly these intersection dimensions from $W$ to $G$.

## Depends on

- [Codes attaining the generalized Singleton bound (LD-MDS codes)](codes-attaining-the-generalized-singleton-bound.md)
- [Higher order MDS codes MDS(l)](higher-order-mds-codes.md)

## Proof depends on

- [Codes attaining the generalized Singleton bound (LD-MDS codes)](codes-attaining-the-generalized-singleton-bound.md)
- [Higher order MDS codes MDS(l)](higher-order-mds-codes.md)

## Sources

- Joshua Brakensiek, Sivakanth Gopi, Visu Makam, "Generic Reed-Solomon codes achieve list-decoding capacity", STOC (2023), SIAM Journal on Computing (2024); arXiv:2206.05256.
- Ron M. Roth, "Higher-order MDS codes", IEEE Transactions on Information Theory 68(12) (2022).
