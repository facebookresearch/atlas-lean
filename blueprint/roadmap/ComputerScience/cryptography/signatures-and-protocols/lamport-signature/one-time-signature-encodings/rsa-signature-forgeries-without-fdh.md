# Forgeries against RSA signatures without a full-domain hash

For unhashed RSA signatures ($\sigma = m^{d} \bmod N$): choosing any $\sigma$ and outputting the message $\sigma^{e} \bmod N$ with signature $\sigma$ is an existential forgery with no signing queries and success probability $1$; and by multiplicativity, signatures on $m_1$ and $m_2$ give the signature $\sigma_1\sigma_2$ on $m_1m_2 \bmod N$. Full-domain hashing in the random oracle model removes these attacks.

## Proof sketch

$(\sigma^e)^d = \sigma$ and $(m_1m_2)^d = m_1^dm_2^d$ modulo $N$.

## Depends on

- [RSA encryption](../../../public-key/rsa-cryptosystem/encrypt.md)
- [Signature forgery experiment](../../../security-games/generic-security-games/sig-game.md)

## Proof depends on

- [Full-domain-hash signatures](../../../public-key/random-oracle-constructions/full-domain-hash-signatures.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
- R. L. Rivest, A. Shamir and L. Adleman, "A Method for Obtaining Digital Signatures and Public-Key Cryptosystems", Communications of the ACM 21(2), 1978.
