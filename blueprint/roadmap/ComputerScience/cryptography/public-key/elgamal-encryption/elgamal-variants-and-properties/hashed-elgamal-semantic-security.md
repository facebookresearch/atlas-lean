# Hashed ElGamal is semantically secure under DDH and a secure KDF

Let hashed ElGamal encapsulate by sending $v = g^\beta$ and deriving the key $H(u^\beta)$ (hashing the shared secret alone), and encrypt the message with a one-time semantically secure symmetric cipher under that key. If DDH holds and $H$ is a secure KDF, the scheme is semantically secure: the advantage is at most $2\,\mathrm{DDHadv} + 2\,\mathrm{KDFadv} + \mathrm{SSadv}$.

## Proof sketch

Replace $u^\beta$ by a uniform group element (DDH), then the derived key by a uniform string (KDF security), after which semantic security of the symmetric cipher applies.

## Depends on

- [Secure key derivation function for a group](secure-key-derivation-function.md)
- [Hybrid encryption](../../key-encapsulation-and-hybrid-encryption/hybrid.md)
- [Advantage of a DDH distinguisher](../ddh-advantage.md)

## Proof depends on

- [Security of hybrid encryption](../../key-encapsulation-and-hybrid-encryption/pub-cpa-advantage-hybrid-le.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
