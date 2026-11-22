# Decomposition of the bit-swap permutation matrix

For every natural number $n$, the pieces $\Pi_{n,0}, \dots, \Pi_{n,n}$ sum to the permutation matrix that swaps two $n$-bit strings: for all $n$-bit strings $x, y, u, v$, the sum $\sum_{i=0}^{n} \Pi_{n,i}[(x, y), (u, v)]$ is $1$ when $u = y$ and $v = x$, and $0$ otherwise. Here $\Pi_{n,i}$ is the integer matrix, indexed by pairs of $n$-bit strings, whose entry at $((x, y), (u, v))$ is the sum, over the sets $S$ of $i$ bit positions, of $\prod_{k \in S} (-s(x_k, y_k)\, s(u_k, v_k)) \prod_{k \notin S} [(x_k, y_k) = (u_k, v_k)]$, where $s$ is the antisymmetric two-bit vector, $s(0, 1) = 1$, $s(1, 0) = -1$ and $s(a, a) = 0$.

## Idea

Swapping two bits is the $4 \times 4$ permutation matrix $P = I - s s^{\mathsf T}$, where $s$ is the antisymmetric vector with entries $(0, 1, -1, 0)$. Swapping two $n$-bit strings is the tensor product of $n$ copies of $P$. Expanding the product $\bigotimes (I - ss^{\mathsf T})$ by choosing, at each position, the identity or the singlet term, and grouping the terms by how many singlet factors they contain, gives the pieces $\Pi_{n,i}$. Each piece has entries bounded by $\binom{n}{i}$, and pieces with more singlet factors than bits vanish.

## Statements

- [Bit-swap pieces sum to the swap permutation matrix](sum-bit-swap-piece.md)
- [Antisymmetric two-bit singlet vector](bit-singlet.md): the antisymmetric two-bit vector
- [Piece of an n-bit swap with i antisymmetric factors](bit-swap-piece.md): the pieces
- [One-bit swap matrix as identity minus singlet outer product](bit-swap-eq-one-sub-vec-mul-vec.md): the one-bit case, $P = I - ss^{\mathsf T}$
- [Bit-swap pieces vanish beyond the number of bits](bit-swap-piece-eq-zero-of-lt.md): pieces beyond $n$ vanish
- [Binomial entry bound for bit-swap pieces](abs-bit-swap-piece-le-choose.md): an entry bound for the pieces
- [Uniform power-of-two entry bound for bit-swap pieces](abs-bit-swap-piece-le-two-pow.md): a weaker, uniform entry bound
