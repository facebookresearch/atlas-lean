# Higher order MDS codes attain the generalized Singleton bound

For every $L \ge 1$, a linear $[n, k]$ code $C$ is $\mathrm{LD}$-$\mathrm{MDS}(\le L)$, i.e. $\big(\frac{L'}{L'+1}\cdot\frac{n-k}{n}, L'\big)$-list decodable for every $L' \le L$, if and only if its dual code $C^{\perp}$ is $\mathrm{MDS}(L+1)$. In particular a code whose dual is $\mathrm{MDS}(L+1)$ attains the generalized Singleton bound for list size $L$; $\mathrm{MDS}(\ell)$ is not preserved under duality for $\ell \ge 4$, so the dual cannot be dropped.

## Proof sketch

Suppose $L + 1$ distinct codewords $c_j = m_j G$ lie within distance $\frac{L}{L+1}(n-k)$ of a word $y$, with agreement sets $A_j$. The vectors $m_j - m_1$ then satisfy linear conditions expressing that they lie in the duals of intersections of the spaces $G_{A_j \cap A_{j'}}$. Equivalently, the differences $c_j - c_1 \in C$ vanish on the pairwise agreement sets, which are conditions on intersections of spans of columns of a parity-check matrix $H$ of $C$, a generator matrix of $C^{\perp}$. For a generic matrix in place of $H$ a dimension count shows these conditions force all $c_j$ to coincide at the stated radius, and $\mathrm{MDS}(L+1)$ of $C^{\perp}$ transfers exactly these intersection dimensions from the generic matrix to $H$; the converse constructs a bad received word from a failing intersection.

## Depends on

- [Codes attaining the generalized Singleton bound (LD-MDS codes)](codes-attaining-the-generalized-singleton-bound.md)
- [Higher order MDS codes MDS(l)](higher-order-mds-codes.md)

## Sources

- Joshua Brakensiek, Sivakanth Gopi, Visu Makam, "Generic Reed-Solomon codes achieve list-decoding capacity", STOC (2023), SIAM Journal on Computing (2024); arXiv:2206.05256.
- Ron M. Roth, "Higher-order MDS codes", IEEE Transactions on Information Theory 68(12) (2022).
