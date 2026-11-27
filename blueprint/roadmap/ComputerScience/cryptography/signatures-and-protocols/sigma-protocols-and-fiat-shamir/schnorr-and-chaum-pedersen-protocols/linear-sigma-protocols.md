# Linear Sigma protocols are complete, special sound and special HVZK

Let $\psi : \mathbb{Z}_q^{k} \to G^{l}$ be a group homomorphism into a group of prime order $q$, with statement $u = \psi(\alpha)$ for a witness $\alpha$. The *linear Sigma protocol* sends $t = \psi(r)$ for uniform $r$, receives a challenge $c \in \mathbb{Z}_q$, replies $z = r + c\alpha$, and accepts iff $\psi(z) = t\,u^{c}$. It is complete, special sound (two accepting conversations $(t, c, z), (t, c', z')$ with $c \ne c'$ give the witness $(z - z')/(c - c')$), and perfectly special HVZK (simulate $t = \psi(z) u^{-c}$ for uniform $z$). With nonces drawn from fair coins within statistical distance $2^{-n}$ of uniform, special HVZK holds statistically with error $2 \cdot 2^{-n}$. Schnorr, Chaum–Pedersen and Okamoto protocols are instances.

## Proof sketch

Linearity of $\psi$ gives completeness and extraction; for HVZK, $z = r + c\alpha$ is uniform for every fixed $c$, and $t$ is determined by $(c, z)$ in both real and simulated conversations.

## Depends on

- [A Sigma protocol](../../zero-knowledge-proofs/sigma-protocol.md)
- [Special soundness of a Sigma protocol](../../zero-knowledge-proofs/special-sound.md)
- [Perfect special honest-verifier zero knowledge](../../zero-knowledge-proofs/special-hvzk.md)
- [Statistical honest-verifier zero knowledge](../../zero-knowledge-proofs/stat-hvzk.md)

## Proof depends on

- [Sampling residues by reducing uniform bit strings](../../../security-games/probabilistic-oracle-programs/sampling-residues-from-fair-bits.md)

## Sources

- U. Maurer, "Unifying Zero-Knowledge Proofs of Knowledge", Progress in Cryptology (AFRICACRYPT 2009), LNCS 5580, 2009.
- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
