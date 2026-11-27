# Soundness of Kilian's protocol from Merkle position binding

In Kilian's four-message argument with $k$ independent repetitions of a PCP verifier whose soundness error is at most $1/2$ per repetition, instantiated with a Merkle commitment that is position binding against strict polynomial-time adversaries, every strict polynomial-time cheating prover that outputs a statement $x \notin L$, a Merkle root and responses has success probability at most

$$
2^{-k} + \nu(\lambda)
$$

for a negligible function $\nu$ of the security parameter $\lambda$. The reduction to position binding runs the prover and rewinds it on polynomially many fresh challenges against one root; two accepted runs that open some common position to different bits yield a collision of the hash. The honest communication is polynomial in the security parameter and, for a verifier with $O(\log |x|)$ random bits and $q$ queries per random string, polylogarithmic in $|x|$: $k$ repetitions times $q$ openings of one bit and a path of $\lceil \log_2 N \rceil$ digests each.

## Proof sketch

Either all accepting runs are consistent with one PCP table, in which case acceptance probability is bounded by the PCP soundness, or two runs disagree on a position, which breaks binding. If the success probability exceeds $2^{-k}$ by a non-negligible amount, rewinding the prover polynomially many times either yields such a pair or recovers a table that the PCP verifier accepts with probability above its soundness error, which is impossible for $x \notin L$.

## Depends on

- [Succinct arguments from probabilistically checkable proofs](../succinct-arguments-from-probabilistically.md)
- [Existential soundness of Merkle inclusion proofs](../../../hash-functions/merkle-trees/verify-sound.md)
- [Probabilistically checkable proofs](../../../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/pcp.md)
- [The collision experiment](../../../hash-functions/birthday-bound/collision-game.md)

## Sources

- Joe Kilian, "A Note on Efficient Zero-Knowledge Proofs and Arguments (Extended Abstract)", Proceedings of the Twenty-Fourth Annual ACM Symposium on Theory of Computing, 1992.
- Boaz Barak and Oded Goldreich, "Universal Arguments and their Applications", Electronic Colloquium on Computational Complexity, 2001.
- Alessandro Chiesa and Eylon Yogev, "Building Cryptographic Proofs from Hash Functions", 2024.
