# Tamo: improved list sizes and generalized Singleton for list size two

Let $\varepsilon > 0$. A folded Reed-Solomon code of rate $R$ with folding parameter $s \ge 16/\varepsilon^2$ is list decodable up to radius $1 - R - \varepsilon$ with list size at most $(1/\varepsilon)^{4/\varepsilon}$. A univariate multiplicity code of rate $R$ over $\mathbb{F}_p$ with order $s \ge 16/\varepsilon^2$ and characteristic $p \ge \max(k, 4/\varepsilon)$ (the definition page already assumes $p \ge k$) is list decodable up to radius $1 - R - \varepsilon$ with list size at most $(1/\varepsilon)^{\frac{4}{\varepsilon}(1 + k/p)} \le (1/\varepsilon)^{8/\varepsilon}$. In both cases a randomized algorithm outputs the list in time polynomial in the code parameters and the list-size bound. Moreover, for every $\varepsilon > 0$ the folded Reed-Solomon code of rate $R$ and length $n$ with folding parameter $s = 1 + \lceil 2R/(3\varepsilon) \rceil$, over an alphabet of size $n^{O(1/\varepsilon)}$, is $\big(\frac{2}{3}(1 - R) - \varepsilon, 2\big)$-list decodable. So folded Reed-Solomon codes asymptotically attain the generalized Singleton bound $\frac{2}{3}(1 - R)$ for list size $2$ over polynomial-size alphabets, the first explicit codes with this property.

## Proof sketch

Bound the number of codewords in an affine subspace of dimension $r$ close to the received word by induction on $r$: a close codeword forces agreement on many coordinates, each imposing a linear condition on the subspace, and a counting of incidences between codewords and coordinates shows the subspace must shrink after a bounded number of codewords.

## Depends on

- [List recovery and relaxed generalized Singleton bounds](list-recovery-of-folded-codes.md)
- [Generalized Singleton bound for list decoding (Shangguan-Tamo)](../generic-reed-solomon-list-decoding-capacity/generalized-singleton-bound-for-list-decoding.md)
- [Folded Reed-Solomon codes](folded-reed-solomon-codes.md)
- [Univariate multiplicity codes](univariate-multiplicity-codes.md)

## Proof depends on

- [Guruswami-Wang: the list of folded RS and multiplicity codes lies in a low-dimensional subspace](linear-algebraic-list-decoding-into-a-subspace.md)

## Sources

- Itzhak Tamo, "Tighter list-size bounds for list-decoding and recovery of folded Reed-Solomon and multiplicity codes", IEEE Transactions on Information Theory (2024); arXiv:2312.17097 (Theorems 1.1, 1.3 and 5.5, Corollaries 3.6 and 3.9).
