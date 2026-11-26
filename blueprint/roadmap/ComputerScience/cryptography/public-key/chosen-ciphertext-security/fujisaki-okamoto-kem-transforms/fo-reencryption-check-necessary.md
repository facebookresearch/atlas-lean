# The re-encryption check of $\mathrm{FO}^{\not\perp}$ is necessary

There is a transformation $\mathrm{PKE} \mapsto \mathrm{PKE}'$ that preserves IND-CPA advantage, $\delta$-correctness and $\gamma$-spreadness, such that the variant of $\mathrm{FO}^{\not\perp}[\mathrm{PKE}', G, H]$ which omits the re-encryption check (decapsulating $c$ to $H(m', c)$ for $m' = \mathrm{Dec}(sk, c)$ without verifying $\mathrm{Enc}(pk, m'; G(m')) = c$) is broken by an efficient adversary with IND-CCA advantage at least $1 - \delta - 1/|\mathcal{K}|$, where $\mathcal{K}$ is the key space of $H$. In $\mathrm{PKE}'$ ciphertexts carry an extra tag $i$, equal to $0$ in honest ciphertexts and ignored by decryption when $i = 0$, while for $i \ge 1$ decryption returns one of two fixed messages encoding the $i$-th bit of the plaintext.

## Proof sketch

For each $i$ the adversary submits the challenge ciphertext $c'_i$ with tag $i$; without re-encryption the decapsulation oracle answers $H(m'_i, c'_i)$, where $m'_i$ is one of two known messages encoding the $i$-th bit of $m^*$, so two queries to $H$ reveal that bit. Having recovered $m^*$, it computes $H(m^*, c^*)$ and compares it with the challenge key. Re-encryption would reject the tagged ciphertext.

## Depends on

- [The KEM transforms $U^{\perp}$ and $U^{\not\perp}$ and the Fujisaki–Okamoto KEMs](transforms-u-and-fo-kems.md)
- [CPA experiment for key encapsulation](../../key-encapsulation-and-hybrid-encryption/kem-game.md)

## Sources

- Dennis Hofheinz, Kathrin Hövelmanns and Eike Kiltz, "A Modular Analysis of the Fujisaki–Okamoto Transformation", Theory of Cryptography (TCC 2017), 2017.
