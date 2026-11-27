# Correctness and implicit rejection of ML-KEM

In ML-KEM with decapsulation key $dk = (dk_{\mathrm{PKE}}, ek, H(ek), z)$: (i) if K-PKE decrypts the honest ciphertext $c = \mathrm{Enc}(ek, m; r)$, where $(K, r) = G(m \,\Vert\, H(ek))$, then decapsulation returns $K$; in particular, if the derived coins keep every coefficient of the K-PKE decryption noise below $B$ with $4B + 2 < q$, decapsulation is correct; (ii) every ciphertext $c'$ for which re-encrypting $m' = \mathrm{Dec}(dk_{\mathrm{PKE}}, c')$ with the derived coins does not reproduce $c'$ decapsulates to the rejection key $J(z \,\Vert\, c')$.

## Proof sketch

Decapsulation recomputes $(K', r') = G(m' \Vert H(ek))$ and compares $\mathrm{Enc}(ek, m'; r')$ with the ciphertext; on an honest ciphertext with $m' = m$ the comparison succeeds and $K' = K$.

## Depends on

- [K-PKE, the public-key encryption scheme inside ML-KEM](k-pke.md)
- [The KEM transforms $U^{\perp}$ and $U^{\not\perp}$ and the Fujisaki–Okamoto KEMs](../../chosen-ciphertext-security/fujisaki-okamoto-kem-transforms/transforms-u-and-fo-kems.md)

## Proof depends on

- [Bounded-noise correctness of K-PKE](k-pke-correctness.md)

## Sources

- National Institute of Standards and Technology, "Module-Lattice-Based Key-Encapsulation Mechanism Standard", National Institute of Standards and Technology, 2024.
