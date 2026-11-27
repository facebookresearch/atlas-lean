# Fiat–Shamir signatures from Sigma protocols are EUF-CMA secure in the random oracle model

Let $\Pi$ be a Sigma protocol for a one-way relation (with key generator $G$) that is special sound and special HVZK, and whose commitments are $\delta$-unpredictable (each commitment value has probability at most $\delta$). The *Fiat–Shamir signature* on $m$ is $(t, z)$ with $c = H(m, t)$ for a random oracle $H$. It is correct whenever $\Pi$ is complete. For every forger making $q_S$ signing and $q_H$ hash queries with success probability $\varepsilon$, the forking reduction finds a witness with probability at least

$$
\frac{\varepsilon'^2}{Q} - \frac{\varepsilon'}{|C|}, \qquad \varepsilon' = \varepsilon - q_S (q_S + q_H)\,\delta, \quad Q = q_H + 1,
$$

where the signing oracle is simulated by programming $H$ at simulated commitments. The same reduction proves soundness of Fiat–Shamir non-interactive proofs. Schnorr signatures (commitments $r g$ are $1/q$-unpredictable) are EUF-CMA secure under the discrete logarithm assumption; reusing related nonces $r$ and $a r + b$ (with known $a, b$) for two messages reveals the signing key, provided the two challenges satisfy $c_1 \ne a c_0$, which fails with probability at most $1/|C|$ when $c_1$ is a fresh random-oracle answer.

## Proof sketch

Simulate signatures with the HVZK simulator and program the oracle; programming fails only if the commitment was queried before, which unpredictability bounds. A forgery uses some oracle answer as its challenge; forking at that query gives two accepting conversations with the same commitment, from which special soundness extracts a witness. For related nonces, the two responses give two linear equations in the nonce and the key, which determine both exactly when $c_1 \ne a c_0$.

## Depends on

- [Signature schemes and (strong) unforgeability in the random oracle model](../random-oracle-signatures/rom-signature-unforgeability.md)
- [A Sigma protocol](../../zero-knowledge-proofs/sigma-protocol.md)
- [Special soundness of a Sigma protocol](../../zero-knowledge-proofs/special-sound.md)
- [Perfect special honest-verifier zero knowledge](../../zero-knowledge-proofs/special-hvzk.md)

## Proof depends on

- [The general forking lemma](../random-oracle-signatures/general-forking-lemma.md)
- [Security of Schnorr signatures in the random oracle model](../../zero-knowledge-and-arguments/security-of-schnorr-signatures-in-the-random.md)

## Sources

- Amos Fiat and Adi Shamir, "How to Prove Yourself: Practical Solutions to Identification and Signature Problems", Advances in Cryptology – CRYPTO '86, 1987.
- Dan Boneh and Victor Shoup, "A Graduate Course in Applied Cryptography", Version 0.6, 2023.
- Mihir Bellare and Gregory Neven, "Multi-Signatures in the Plain Public-Key Model and a General Forking Lemma", Proceedings of the 13th ACM Conference on Computer and Communications Security, 2006.
- David Pointcheval and Jacques Stern, "Security Arguments for Digital Signatures and Blind Signatures", Journal of Cryptology, 2000.
