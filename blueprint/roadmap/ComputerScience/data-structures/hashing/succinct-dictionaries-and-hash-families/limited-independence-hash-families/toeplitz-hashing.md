# Toeplitz hashing is pairwise independent

Let $F$ be a finite field (including $F = \mathbb{F}_2$, i.e. bit strings) and $m, n \ge 1$. For an $m \times n$ Toeplitz matrix $T$ (constant along diagonals, determined by $n + m - 1$ entries) and a vector $v \in F^m$, let $h_{T,v}(x) = Tx + v$. With $T$ and $v$ independent and uniform, the family $\{h_{T,v}\}$ from $F^n$ to $F^m$ is pairwise independent, using seeds of $n + 2m - 1$ field elements instead of the $mn + m$ of the full affine family.

## Proof sketch

By the shift criterion it suffices that for every nonzero $d \in F^n$ the map $T \mapsto Td$ is onto $F^m$. If $j$ is the last nonzero coordinate of $d$, then entry $r$ of $Td$ involves the diagonal parameter of index $r - j$ with coefficient $d_j \ne 0$ plus parameters of larger index, so the system can be solved row by row.

## Depends on

- [Pairwise-independent hashing by affine maps over GF(2)](../../../../../TheoryOfComputation/counting-complexity/counting-and-the-polynomial-hierarchy/pairwise-independent-hashing-by-affine-maps.md)
- [k-wise independent hash family](../word-ram-hash-families/k-wise-independent-hash-family.md)

## Proof depends on

- [Pairwise independence, universality and the shift criterion](pairwise-independence-and-the-shift-criterion.md)

## Sources

- Y. Mansour, N. Nisan and P. Tiwari, "The Computational Complexity of Universal Hashing", Theoretical Computer Science 107(1), 1993.
- H. Krawczyk, "LFSR-based Hashing and Authentication", Advances in Cryptology (CRYPTO 1994), LNCS 839, 1994.
- J. Katz and Y. Lindell, "Introduction to Modern Cryptography", CRC Press, 2020.
