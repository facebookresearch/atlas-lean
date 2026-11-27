# Encrypt-then-MAC with an unauthenticated IV loses ciphertext integrity

Let the cipher be the one-block PRF cipher $m \mapsto r \,\|\, (F(k, r) \oplus m)$ with uniform $r$, and let the MAC be applied only to the body $F(k,r) \oplus m$, not to $r$. Then the resulting encrypt-then-MAC scheme has neither ciphertext integrity nor authenticated-encryption security, for every MAC: after one encryption query, replacing $r$ by any $r' \ne r$ while keeping the body and tag yields a new valid ciphertext.

## Proof sketch

The tag verifies on the unchanged body, so decryption accepts the modified ciphertext, which differs from the oracle's reply.

## Depends on

- [Authenticated encryption](authenticated-encryption.md)
- [Encrypt-then-authenticate](../encrypt-then-mac/scheme.md)

## Sources

- Chanathip Namprempre, Phillip Rogaway and Thomas Shrimpton, "Reconsidering Generic Composition", Advances in Cryptology - EUROCRYPT 2014, Lecture Notes in Computer Science, Springer, 2014.
