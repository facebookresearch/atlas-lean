# The re-encryption check of $\mathrm{FO}^{\not\perp}$ is necessary

There is a transformation $\mathrm{PKE} \mapsto \mathrm{PKE}'$ that preserves IND-CPA advantage, $\delta$-correctness and $\gamma$-spreadness, such that the variant of $\mathrm{FO}^{\not\perp}[\mathrm{PKE}', G, H]$ which omits the re-encryption check (decapsulating $c$ to $H(m', c)$ for $m' = \mathrm{Dec}(sk, c)$ without verifying $\mathrm{Enc}(pk, m'; G(m')) = c$) is broken by an efficient adversary with IND-CCA advantage close to $1$. In $\mathrm{PKE}'$ ciphertexts carry an extra tag that decryption ignores honestly but that lets a mauled challenge ciphertext decrypt to the challenge plaintext.

## Proof sketch

The adversary submits the challenge ciphertext with its tag modified; without re-encryption the decapsulation oracle answers $H(m^*, c')$, and querying $H$ at the plaintext it recovers the derivation of the real key, so it compares with the challenge key. Re-encryption would reject the tagged ciphertext.

## Depends on

- [The KEM transforms $U^{\perp}$ and $U^{\not\perp}$ and the Fujisaki–Okamoto KEMs](transforms-u-and-fo-kems.md)
- [CPA experiment for key encapsulation](../../key-encapsulation-and-hybrid-encryption/kem-game.md)

## Sources

- Dennis Hofheinz, Kathrin Hövelmanns and Eike Kiltz, "A Modular Analysis of the Fujisaki–Okamoto Transformation", Theory of Cryptography (TCC 2017), 2017.
