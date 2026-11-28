# Variable-length MACs from fixed-length MACs

Let $\Pi = (\mathrm{Mac}, \mathrm{Vrfy})$ be a MAC for messages of length $L$, with $L$ super-logarithmic in the security parameter (so $2^{-L/4}$ is negligible). The *blockwise construction* splits a message $m$ of length less than $2^{L/4}$ into blocks $m_1, \dots, m_d$ of $L/4$ bits (padding the last), draws a fresh random identifier $r$ of $L/4$ bits, and tags each block as $t_i = \mathrm{Mac}_k(r \Vert \ell \Vert i \Vert m_i)$ with $\ell$ the message length; the tag is $(r, t_1, \dots, t_d)$. If $\Pi$ is EUF-CMA secure and its message length is computable in polynomial time, the construction is EUF-CMA secure for messages of arbitrary (polynomially bounded) length.

## Proof sketch

Polynomially many uniform identifiers of $L/4$ bits repeat only with negligible probability. If identifiers never repeat, a forgery on a new message must contain a block tag on a string $r \Vert \ell \Vert i \Vert m_i$ never queried to $\mathrm{Mac}$, because the identifier, length and index together prevent mixing blocks from different tagged messages; this is a forgery against $\Pi$.

## Depends on

- [The MAC forgery experiment](../pseudorandom-functions/mac-game.md)
- [Polynomial-query unforgeability of MACs](../../security-games/asymptotic-security/poly-query-macsecure.md)
- [Negligible advantage](../../security-games/asymptotic-security/negligible-adv.md)

## Sources

- Jonathan Katz and Yehuda Lindell, "Introduction to Modern Cryptography", CRC Press, 2020.
