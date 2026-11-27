# Malleability of random-IV stream encryption

Let a cipher encrypt $m$ as $c = \mathrm{IV} \,\|\, (\mathrm{ks}(k, \mathrm{IV}, |m|) \oplus m)$ for a uniform IV and any keystream function (randomized CTR, OFB and the one-block PRF cipher have this form). For every mask $\Delta$ with $|\Delta| \ge |m|$, the ciphertext obtained by keeping the IV and XORing $\Delta$ (truncated) into the body is a valid encryption of $m \oplus \Delta$ under the same key and IV, and it decrypts to $m \oplus \Delta$. The transformation uses neither the key nor the keystream and runs in polynomial time; hence such ciphers are not CCA secure.

## Proof sketch

XOR commutes: $(\mathrm{ks} \oplus m) \oplus \Delta = \mathrm{ks} \oplus (m \oplus \Delta)$, and decryption recomputes the same keystream from the unchanged IV.

## Depends on

- [Private-key encryption scheme](../../security-games/generic-security-games/symm-enc-scheme.md)
- [CCA indistinguishability experiment](../../security-games/generic-security-games/cca-game.md)

## Sources

- Jonathan Katz and Moti Yung, "Unforgeable Encryption and Chosen Ciphertext Secure Modes of Operation", Fast Software Encryption (FSE 2000), LNCS 1978, Springer, 2001, pp. 284–299, Sections 2 and 3.3.
