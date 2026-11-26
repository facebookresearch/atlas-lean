# Identification schemes from Sigma protocols

A Sigma protocol $\Pi$ for $\mathcal{R}$ with a key generator $G$ sampling $(x, y) \in \mathcal{R}$ is an identification scheme with public key $y$. (i) *Direct attacks:* if $\Pi$ is special sound and the relation is one-way for $G$ (no efficient algorithm finds a witness for $y$), then every impersonator succeeds with probability at most $1/|C| + \sqrt{\mathrm{Adv}^{\mathrm{ow}}}$; more precisely, with $\varepsilon$ its success probability, the rewinding reduction finds a witness with probability at least $\varepsilon^2 - \varepsilon/|C|$. (ii) *Eavesdropping attacks:* if $\Pi$ is special HVZK, an adversary that also sees polynomially many honest transcripts has exactly the success probability of a direct-attack adversary that simulates them itself. Schnorr identification (with $\alpha$ uniform and $u = \alpha g$) is therefore secure against eavesdropping attacks under the discrete logarithm assumption.

## Proof sketch

(i) Rewind the impersonator at the challenge. (ii) Honest transcripts are distributed exactly as simulated ones, which the adversary can generate from $y$.

## Depends on

- [A Sigma protocol](../../zero-knowledge-proofs/sigma-protocol.md)
- [Special soundness of a Sigma protocol](../../zero-knowledge-proofs/special-sound.md)
- [Perfect special honest-verifier zero knowledge](../../zero-knowledge-proofs/special-hvzk.md)
- [Discrete-logarithm experiment](../../../public-key/hardness-assumptions/dlog-game.md)

## Proof depends on

- [The rewinding lemma](../../zero-knowledge-and-arguments/the-rewinding-lemma.md)
- [Special-sound Sigma protocols are proofs of knowledge with a PPT rewinding extractor](../sigma-protocol-theory/sigma-protocol-proof-of-knowledge.md)

## Sources

- Dan Boneh and Victor Shoup, "A Graduate Course in Applied Cryptography", Version 0.6, 2023.
- Claus-Peter Schnorr, "Efficient Signature Generation by Smart Cards", Journal of Cryptology, 1991.
