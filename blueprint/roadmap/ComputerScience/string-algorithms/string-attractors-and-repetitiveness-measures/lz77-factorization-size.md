# Size $z$ of the greedy LZ77 factorization

The *LZ77 factorization* of $T[1..n]$ is $T = f_1 f_2 \cdots f_z$, built greedily from left to right: if the next phrase starts at position $p$, then $f$ is the longest prefix of $T[p..n]$ that also occurs starting at some position $p' < p$ (the occurrence may overlap $f$), or the single letter $T[p]$ if no such prefix is nonempty. The number of phrases is denoted $z(T)$. The greedy factorization minimizes the number of phrases among all factorizations in which every phrase is either a single letter or has an earlier occurrence.

## Sources

- Abraham Lempel, Jacob Ziv, "On the Complexity of Finite Sequences", IEEE Transactions on Information Theory 22(1) (1976).
- Dominik Kempa, Nicola Prezza, "At the Roots of Dictionary Compression: String Attractors", STOC (2018), arXiv:1710.10964.
