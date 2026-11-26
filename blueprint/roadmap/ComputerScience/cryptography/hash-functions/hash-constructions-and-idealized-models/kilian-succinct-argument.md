# Kilian's argument: committing to a PCP proof with a Merkle tree

Let $V$ be a PCP verifier for a language $L$ with logarithmic randomness and constant query complexity, and $H$ a collision-resistant keyed hash. In Kilian's protocol the verifier sends a uniform hash key $k$; the prover sends $x$ and the Merkle root of its PCP proof under $H_k$; the verifier sends $\lambda$ independent PCP random strings, where $\lambda$ is the security parameter; the prover opens the queried positions with authentication paths; the verifier accepts iff all paths verify and $V$ accepts on every random string. The protocol is complete and is an argument with negligible soundness error against efficient provers, with communication polynomial in the security parameter and logarithmic in the proof length.

## Proof sketch

By multi-opening extraction, an efficient prover is bound to a single proof table except with negligible probability; soundness then reduces to the PCP soundness, amplified by the independent repetitions.

## Depends on

- [Interactive arguments](../../signatures-and-protocols/zero-knowledge-and-arguments/interactive-arguments.md)
- [The PCP theorem: NP = PCP(O(log n), O(1))](../../../../TheoryOfComputation/pcp-and-inapproximability/pcp-theorem.md)
- [Merkle root](../merkle-trees/root.md)

## Proof depends on

- [Extraction from multi-opening Merkle commitments](merkle-tree-multi-opening-extraction.md)
- [Succinct arguments from probabilistically checkable proofs](../../signatures-and-protocols/zero-knowledge-and-arguments/succinct-arguments-from-probabilistically.md)

## Sources

- J. Kilian, "A Note on Efficient Zero-Knowledge Proofs and Arguments", Proceedings of the 24th Annual ACM Symposium on Theory of Computing (STOC), 1992.
- B. Barak and O. Goldreich, "Universal Arguments and their Applications", Proceedings of the 17th IEEE Conference on Computational Complexity (CCC), 2002.
