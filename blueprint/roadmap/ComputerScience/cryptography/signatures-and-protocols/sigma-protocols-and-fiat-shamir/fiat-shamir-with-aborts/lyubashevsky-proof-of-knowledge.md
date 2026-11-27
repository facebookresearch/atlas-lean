# Lyubashevsky identification is a proof of knowledge of short SIS solutions

Lyubashevsky's identification protocol with $k$-bit challenges has special soundness for a relaxed relation: from two accepting transcripts $(t, c, z)$ and $(t, c', z')$ with $c \ne c'$ one computes, in polynomial time, $(z - z', c - c')$, a nonzero integer vector in the kernel of $[\,A \mid -T\,]$ with $\|z - z'\|_\infty \le 2(\gamma - \beta)$ and $c - c' \in \{-1, 0, 1\}^k$. Consequently there is a strict probabilistic polynomial-time rewinding extractor such that, for every statement and every prover convincing the verifier with probability $\varepsilon$, the extractor outputs such a relaxed witness with probability at least $\varepsilon^2 - \varepsilon/2^k$. Moreover, if a genuine witness $S$ with $\|S\|_\infty \le \eta$ is known and the extracted vector $v$ satisfies $A v \equiv \Delta c\, T$ with $v \ne S\Delta c$, then $v - S\Delta c$ is a nonzero homogeneous SIS solution with bound $2(\gamma - \beta) + k\eta$.

## Proof sketch

Subtracting the verification equations gives $A(z - z') \equiv T(c - c')$. The extractor runs the prover twice with the same coins and independent challenges; the rewinding lemma bounds the probability of two accepting runs with distinct challenges.

## Depends on

- [Lyubashevsky's lattice identification protocol](lyubashevsky-identification.md)
- [The short integer solution problem (SIS)](../../../public-key/lattice-and-code-based-cryptography/lattice-problems/short-integer-solution-problem.md)
- [Special soundness of a Sigma protocol](../../zero-knowledge-proofs/special-sound.md)
- [Knowledge soundness](../../zero-knowledge-and-arguments/knowledge-soundness.md)

## Proof depends on

- [The rewinding lemma](../../zero-knowledge-and-arguments/the-rewinding-lemma.md)

## Sources

- Vadim Lyubashevsky, "Lattice Signatures without Trapdoors", Advances in Cryptology – EUROCRYPT 2012, 2012.
