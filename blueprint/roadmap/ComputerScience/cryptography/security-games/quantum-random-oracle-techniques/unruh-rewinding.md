# Unruh's quantum rewinding lemma for special-sound protocols

Let $\Sigma$ be a Sigma protocol with challenge space $C$ that is special sound and has *strict soundness* (for each commitment and challenge at most one accepting response), and let a quantum prover make the verifier accept with probability $\epsilon$. Then a quantum extractor that runs the prover on a random challenge, measures the response, applies the inverse of the prover's unitary, and runs it again on a fresh challenge obtains two accepting transcripts with distinct challenges with probability at least $\epsilon^{3}-\epsilon/|C|$. Hence such protocols are quantum proofs of knowledge, and the strict soundness condition can be relaxed to collapsing responses.

## Proof sketch

The response measurement on an accepting branch is almost non-disturbing because strict soundness makes the accepting response unique given the challenge, so uncomputing returns close to the original state. Jordan's lemma-type analysis of two projectors (accept on challenge $c$, accept on $c'$) yields the cubic bound via Jensen's inequality.

## Depends on

- [Collapsing hash functions and collapse-binding commitments](collapsing-hash.md)
- [Knowledge soundness](../../signatures-and-protocols/zero-knowledge-and-arguments/knowledge-soundness.md)

## Proof depends on

- [The rewinding lemma](../../signatures-and-protocols/zero-knowledge-and-arguments/the-rewinding-lemma.md)

## Sources

- Dominique Unruh, "Quantum Proofs of Knowledge", EUROCRYPT (2012).
- Dominique Unruh, "Computationally Binding Quantum Commitments", EUROCRYPT (2016), IACR ePrint 2015/361.
