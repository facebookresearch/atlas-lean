# The graph 3-coloring zero-knowledge protocol with Naor commitments

Let $G = (V, E)$ be a graph with $E \ne \emptyset$, let the prover hold a proper 3-coloring $\phi : V \to \{1, 2, 3\}$, and let $G_n : \{0,1\}^n \to \{0,1\}^{3n}$ be a pseudorandom generator used for Naor's bit commitment, a color being committed bit by bit through a fixed two-bit encoding. One execution of the protocol is: (V0) the verifier sends a uniform $R \in \{0,1\}^{3n}$; (P1) the prover picks a uniformly random permutation $\pi$ of $\{1, 2, 3\}$ and sends, for every vertex $v$, a commitment under $R$ to the color $\pi(\phi(v))$, using fresh independent seeds; (V1) the verifier sends a uniformly random edge $(u, v) \in E$; (P2) the prover opens the commitments of $u$ and $v$; (V2) the verifier accepts the execution if both openings are valid and reveal two different elements of $\{1, 2, 3\}$, and rejects otherwise. Goldreich, Micali and Wigderson repeat the execution $|E|^2$ times with independent coins, and the verifier accepts if every execution accepts.

## Depends on

- [Zero-knowledge interactive proofs](../zero-knowledge-interactive-proofs.md)
- [Naor's bit commitment from a pseudorandom generator](../../commitment-schemes/commitments-and-zero-knowledge-for-np/naor-bit-commitment.md)

## Sources

- O. Goldreich, S. Micali and A. Wigderson, "Proofs that Yield Nothing but Their Validity or All Languages in NP Have Zero-Knowledge Proof Systems", Journal of the ACM 38(3), 1991: Section 3.1, Protocol 4 (stated with a secure encryption function in the role of the commitment, $|E|^2$ iterations).
- O. Goldreich, "Foundations of Cryptography, Volume 1: Basic Tools", Cambridge University Press, 2001: Section 4.4.2, Construction 4.4.7 (stated for any bit commitment scheme; the remarks closing Section 4.4.2 note that Naor's commitment may be used).
- M. Naor, "Bit Commitment Using Pseudorandomness", Journal of Cryptology 4(2), 1991.
