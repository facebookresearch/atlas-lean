# Zero knowledge and completeness of Fiat–Shamir non-interactive proofs

Let $\Pi$ be special HVZK with $\delta$-unpredictable commitments. The Fiat–Shamir non-interactive proof for $y$ is $(t, z)$ with $c = H(y, t)$. In the lazy random oracle model it is perfectly complete for every $(x, y) \in \mathcal{R}$. It is zero knowledge: the simulator that, for each proof request, runs the special HVZK simulator on a fresh uniform challenge and programs $H(y, t) := c$ (aborting on conflict) is indistinguishable from the real prover, with distinguishing advantage at most

$$
q_P (q_P + q_H)\,\delta
$$

for an adversary making $q_P$ proof and $q_H$ hash queries.

## Proof sketch

Real and simulated worlds agree until the simulator tries to program a point already defined, which happens for each proof with probability at most $(q_P + q_H)\delta$.

## Depends on

- [A Sigma protocol](../../zero-knowledge-proofs/sigma-protocol.md)
- [Perfect special honest-verifier zero knowledge](../../zero-knowledge-proofs/special-hvzk.md)
- [The random oracle model](../../../public-key/random-oracle-constructions/the-random-oracle-model.md)
- [Security of the Fiat–Shamir transform](../../zero-knowledge-and-arguments/security-of-the-fiatshamir-transform.md)

## Proof depends on

- [The difference lemma](../../../security-games/games-and-advantages/advantage-le-win-prob-of-eq-of-not-bad.md)

## Sources

- Amos Fiat and Adi Shamir, "How to Prove Yourself: Practical Solutions to Identification and Signature Problems", Advances in Cryptology – CRYPTO '86, 1987.
- Dan Boneh and Victor Shoup, "A Graduate Course in Applied Cryptography", Version 0.6, 2023.
