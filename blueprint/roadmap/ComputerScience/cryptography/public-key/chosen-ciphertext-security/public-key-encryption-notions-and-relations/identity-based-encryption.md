# Identity-based encryption and its security notions

An *identity-based encryption* scheme has setup producing master keys $(mpk, msk)$, key extraction $sk_{\mathrm{id}} \leftarrow \mathrm{Ext}(msk, \mathrm{id})$, encryption $E(mpk, \mathrm{id}, m)$, and decryption with $sk_{\mathrm{id}}$. It is *semantically secure* if efficient adversaries that may adaptively obtain secret keys for identities of their choice have negligible advantage in distinguishing encryptions of two equal-length messages under a challenge identity whose key they never request; *selective* security requires the challenge identity to be fixed before seeing $mpk$, and *anonymous (private)* security additionally hides the identity.

## Depends on

- [Public-key encryption scheme](../../../security-games/generic-security-games/pkescheme.md)
- [Security of the Boneh–Franklin identity-based encryption scheme](../../advanced-encryption-and-pairings/security-of-the-bonehfranklin-identity-based.md)

## Sources

- D. Boneh and M. Franklin, "Identity-Based Encryption from the Weil Pairing", Advances in Cryptology (CRYPTO 2001), LNCS 2139, 2001.
- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
