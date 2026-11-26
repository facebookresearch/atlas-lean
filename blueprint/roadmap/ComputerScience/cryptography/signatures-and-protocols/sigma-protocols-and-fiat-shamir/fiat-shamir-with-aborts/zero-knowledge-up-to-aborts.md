# Zero knowledge up to aborts

Let a Sigma protocol with aborts be non-abort special honest-verifier zero knowledge. Then with a uniform challenge the simulator reproduces the accepted view of an honest conversation exactly: the probability of abort and the joint law of $(t, c, z)$ on non-aborting runs coincide with those of the real prover with any valid witness. If moreover two witnesses for the same statement give equal commitment marginals, they give identical full transcript laws, including the commitments of aborted attempts, and this persists when the challenge is any common public function of the commitment.

## Proof sketch

Averaging the per-challenge equality of accepted views over the uniform challenge gives the first claim; the second follows because a full transcript is determined by its commitment marginal and its erased-abort law.

## Depends on

- [Sigma protocols with aborts](sigma-protocols-with-aborts.md)

## Sources

- Vadim Lyubashevsky, "Lattice Signatures without Trapdoors", Advances in Cryptology – EUROCRYPT 2012, 2012.
- Manuel Barbosa et al., "Fixing and Mechanizing the Security Proof of Fiat-Shamir with Aborts and Dilithium", Cryptology ePrint Archive, Paper 2023/246, 2023.
