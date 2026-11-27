# HMAC

For an iterated hash $H$ with block size $B$ bytes and a key $K$ (hashed first if longer than $B$, then zero-padded to $B$ bytes), the HMAC of a message $m$ is

$$\mathrm{HMAC}(K, m) = H\bigl((K \oplus \mathrm{opad}) \,\|\, H((K \oplus \mathrm{ipad}) \,\|\, m)\bigr),$$

with $\mathrm{ipad} = \mathtt{0x36}^B$ and $\mathrm{opad} = \mathtt{0x5c}^B$. MGF1 is the related mask generation function $\mathrm{MGF1}(z, \ell)$, defined as the first $\ell$ bytes of $H(z \| \langle 0 \rangle_4) \| H(z \| \langle 1\rangle_4) \| \cdots$.

## Depends on

- [Merkle–Damgård hash with length strengthening](../merkle-damg-rd-construction/hash.md)
- [Message authentication code](../../security-games/generic-security-games/macscheme.md)

## Sources

- H. Krawczyk, M. Bellare and R. Canetti, "HMAC: Keyed-Hashing for Message Authentication", RFC 2104, 1997.
- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
