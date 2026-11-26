# XOR-hash from a pseudorandom function

Let $F$ be a PRF from position-tagged blocks to $\{0,1\}^w$. The *XOR-hash* of a message $m = m_1 \| \cdots \| m_\ell$ of at most $L$ fixed-width blocks is

$$H_k(m) = \bigoplus_{j=1}^{\ell} F\bigl(k, (j, m_j)\bigr).$$

## Depends on

- [PRF advantage](../pseudorandom-functions/prf-advantage.md)
- [Computational universal hash function](computational-universal-hash.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
