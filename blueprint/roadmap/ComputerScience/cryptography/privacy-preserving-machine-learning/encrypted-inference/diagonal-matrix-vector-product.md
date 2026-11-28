# The diagonal method for a plaintext matrix times an encrypted vector

For an $n\times n$ matrix $A$ over a commutative ring and a vector $v$ indexed by $\mathbb{Z}/n$, $Av=\sum_{i=0}^{n-1}d_i\odot(v\lll i)$, where $d_i[j]=A_{j,j+i}$ is the $i$-th generalized diagonal and $(v\lll i)[j]=v[j+i]$. With packed encryption this costs $n-1$ ciphertext rotations, $n$ plaintext products and one multiplicative level.

Let $R$ be a commutative ring, $A\in R^{n\times n}$ and $v\in R^n$, all indices taken modulo $n$. Define $d_i=(A_{0,i},A_{1,i+1},\dots,A_{n-1,i-1})$ and the left rotation $(v\lll i)[j]=v[j+i]$. Then for every $j$,

$$
(Av)[j]=\sum_{i=0}^{n-1}d_i[j]\,(v\lll i)[j]=\sum_{i=0}^{n-1}A_{j,j+i}\,v[j+i] .
$$

Consequently, in a packed scheme with $n$ slots over $R=\mathbb{Z}_p$ whose slot permutations include all cyclic rotations, a ciphertext $[v]$ and plaintext diagonals $d_0,\dots,d_{n-1}$ give

$$
[Av]=\sum_{i=0}^{n-1}\mathrm{SIMDScMult}(\mathrm{Perm}([v],\lll i),d_i),
$$

using $n-1$ non-trivial rotations, $n$ plaintext–ciphertext products and $n-1$ additions, with depth one multiplication and one rotation, and the whole output packed in a single ciphertext. All rotations act on the input ciphertext, which is what allows their common work to be shared ("hoisting"). For the half-rotation group of power-of-two cyclotomics the diagonals are taken along the available permutations instead.

## Depends on

- [Packed additively homomorphic encryption](packed-additively-homomorphic-encryption.md)

## Proof depends on

None.

## Expansion

As $i$ runs over $\mathbb{Z}/n$, the column index $k=j+i$ runs over $\mathbb{Z}/n$ once, so the sum is $\sum_kA_{j,k}v[k]$. The homomorphic form follows from correctness of $\mathrm{SIMDAdd}$, $\mathrm{SIMDScMult}$ and $\mathrm{Perm}$; noise accounting is outside this statement.

## Sources

- Xiaoqian Jiang, Miran Kim, Kristin Lauter, Yongsoo Song, "Secure Outsourced Matrix Computation and Application to Neural Networks", ACM CCS 2018, DOI 10.1145/3243734.3243837, [authors' copy](https://yongsoosong.github.io/files/papers/matrix.pdf), §2.2 (plaintext slots in $R^n$ over a ring $R$), §2.3, Equation (1) and Algorithm 1: the identity for $U\in R^{n\times n}$, with $\rho(m;\ell)=(m_\ell,\dots,m_{n-1},m_0,\dots,m_{\ell-1})$.
- Shai Halevi, Victor Shoup, "Algorithms in HElib", CRYPTO 2014, LNCS 8616, DOI 10.1007/978-3-662-44371-2_31; numbers from IACR ePrint 2014/106: §4.3 ("Matrix in diagonal order"), for slots in a finite field.
- Chiraag Juvekar, Vinod Vaikuntanathan, Anantha Chandrakasan, "GAZELLE: A Low Latency Framework for Secure Neural Network Inference", 27th USENIX Security Symposium (2018), [USENIX copy](https://www.usenix.org/conference/usenixsecurity18/presentation/juvekar); preprint arXiv:1801.05507v1. Section 5 ("The Diagonal Method"), for slots in $\mathbb{Z}_p$ and the ciphertext operation count.
