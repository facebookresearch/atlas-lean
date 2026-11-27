# Zero knowledge up to aborts

Let a Sigma protocol with aborts be non-abort special honest-verifier zero knowledge. Then with a uniform challenge the simulator reproduces the accepted view of an honest conversation exactly: the probability of abort and the joint law of $(t, c, z)$ on non-aborting runs coincide with those of the real prover with any valid witness. If moreover two witnesses for the same statement give equal commitment marginals, they give identical full transcript laws, including the commitments of aborted attempts, and this persists when the challenge is any common public function of the commitment.

## Proof sketch

Averaging the per-challenge equality of accepted views over the uniform challenge gives the first claim; for the second, the full transcript law is recovered from the commitment marginal and the accepted view. The commitment $t$ is drawn before the challenge, so its law $P(t)$ does not depend on $c$; for each challenge $c$ and commitment $t$ the accepted view gives $P(t, z \mid c)$ for every response $z$, and the aborted runs with commitment $t$ have probability $P(t, \bot \mid c) = P(t) - \sum_z P(t, z \mid c)$. By the first claim both witnesses have the simulator's accepted view, so equal commitment marginals give equal per-challenge laws of (commitment, answer), aborts included. If the challenge is $c = h(t)$ for a public function $h$, the law of the prover's state given $t$ does not involve the challenge, so the joint law of $(t, \text{answer})$ is $P(t, \cdot \mid c = h(t))$, obtained by substituting $c = h(t)$ into these per-challenge laws, and it is again the same for both witnesses.

## Depends on

- [Sigma protocols with aborts](sigma-protocols-with-aborts.md)

## Sources

- Vadim Lyubashevsky, "Lattice Signatures without Trapdoors", Advances in Cryptology – EUROCRYPT 2012, 2012.
- Manuel Barbosa et al., "Fixing and Mechanizing the Security Proof of Fiat-Shamir with Aborts and Dilithium", Cryptology ePrint Archive, Paper 2023/246, 2023.
