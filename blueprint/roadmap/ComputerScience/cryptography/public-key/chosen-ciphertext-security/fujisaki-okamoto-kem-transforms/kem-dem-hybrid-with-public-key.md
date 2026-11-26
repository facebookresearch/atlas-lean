# KEM–DEM hybrid encryption needs KEM security against distinguishers that see the public key

Let a KEM be secure in the sense that no efficient distinguisher, given the public key $pk$, the encapsulation $c$ and a key $K_b$ (the encapsulated key for $b = 0$, a uniform key for $b = 1$), guesses $b$ with non-negligible advantage, and let the data-encapsulation mechanism (DEM) be one-time semantically secure. Then KEM–DEM hybrid encryption $\mathrm{Enc}(pk, m) = (c, \mathrm{Enc}^{\mathrm{DEM}}_K(m))$ is IND-CPA secure, with advantage at most twice the KEM advantage plus the DEM advantage. The public key in the KEM experiment is necessary: if the KEM distinguisher sees only $(K_b, c)$, the implication fails — with key generation outputting a uniform $pk$ with $sk = pk$ and encapsulation returning $K = pk$ with empty $c$, both KEM experiments show a uniform key and an empty encapsulation, yet the hybrid scheme encrypts under a key contained in the public key and is trivially insecure.

## Proof sketch

Hybrid 1 replaces the encapsulated key by a uniform key, at the cost of the KEM advantage; the reduction needs $pk$ to answer the adversary. In the hybrid world the DEM key is independent of the adversary's view, so the DEM's one-time security applies. The counterexample is a direct computation.

## Depends on

- [Key-encapsulation mechanism](../../key-encapsulation-and-hybrid-encryption/kemscheme.md)
- [CPA experiment for key encapsulation](../../key-encapsulation-and-hybrid-encryption/kem-game.md)
- [Hybrid encryption](../../key-encapsulation-and-hybrid-encryption/hybrid.md)
- [CPA security of public-key encryption families](../../../security-games/asymptotic-security/pub-cpasecure.md)

## Proof depends on

- [Security of hybrid encryption](../../key-encapsulation-and-hybrid-encryption/pub-cpa-advantage-hybrid-le.md)

## Sources

- Dan Boneh and Victor Shoup, "A Graduate Course in Applied Cryptography", Version 0.6, 2023.
- Jonathan Katz and Yehuda Lindell, "Introduction to Modern Cryptography", CRC Press, 2020.
