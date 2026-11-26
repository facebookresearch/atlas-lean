# XOR-hash from a pseudorandom function

Let $F$ be a PRF from position-tagged blocks to $\{0,1\}^w$. The *XOR-hash* of a message $m = m_1 \| \cdots \| m_\ell$ of at most $L$ fixed-width blocks is

$$H_k(m) = \bigoplus_{j=1}^{\ell} F\bigl(k, (j, m_j)\bigr).$$

This is the message-dependent part of the tag of the XOR MACs, which additionally XORs in $F(k, (0, r))$ for a seed or counter $r$; there the tagged input $(j, m_j)$ is encoded as the bit $1$, the index $j$ and the block $m_j$.

## Depends on

- [PRF advantage](../pseudorandom-functions/prf-advantage.md)
- [Computational universal hash function](computational-universal-hash.md)

## Sources

- M. Bellare, R. Guérin and P. Rogaway, "XOR MACs: New Methods for Message Authentication Using Finite Pseudorandom Functions", Advances in Cryptology – CRYPTO '95, LNCS 963, Springer, 1995 (the tag function of the XOR schemes).
