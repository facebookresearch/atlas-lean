# Completeness and soundness of the graph 3-coloring protocol with Naor commitments

In one execution of the graph 3-coloring protocol with Naor commitments on $G = (V, E)$ with $E \ne \emptyset$: (i) if the prover follows the protocol with a proper 3-coloring, the verifier accepts with probability $1$; (ii) if $G$ is not 3-colorable, then no prover, even computationally unbounded, makes the verifier accept with probability greater than $1 - 1/|E| + 2^{-n}$, where $2^{-n}$ bounds the probability that the verifier's string $R$ lets some commitment be opened to both $0$ and $1$. Over $k$ sequential executions with fresh coins, a non-3-colorable graph is accepted with probability at most $(1 - 1/|E| + 2^{-n})^k$. With a perfectly binding commitment, as in the protocol of Goldreich, Micali and Wigderson, the term $2^{-n}$ disappears, and their $|E|^2$ iterations accept a non-3-colorable graph with probability at most $(1 - 1/|E|)^{|E|^2} \le e^{-|E|}$.

## Proof sketch

Completeness: the opened colors are $\pi(\phi(u)) \ne \pi(\phi(v))$. Soundness: with probability at least $1 - 2^{-n}$ the string $R$ admits no commitment with two valid openings, and then the commitments fix at most one value per vertex. Since $G$ is not 3-colorable, some edge has endpoints whose committed values are not two different elements of $\{1, 2, 3\}$ (or cannot be opened at all), and the verifier picks that edge, and rejects, with probability at least $1/|E|$. For sequential executions, bound each execution's acceptance probability conditioned on the history; the verifier's fresh $R$ and edge are independent of it.

## Depends on

- [The graph 3-coloring zero-knowledge protocol with Naor commitments](masked-3sat-zero-knowledge-protocol.md)

## Proof depends on

- [Naor's commitment is computationally hiding and statistically binding](../../commitment-schemes/commitments-and-zero-knowledge-for-np/naor-commitment-security.md)
- [Soundness of the graph 3-coloring protocol](../soundness-of-the-graph-3-coloring-protocol.md)

## Sources

- O. Goldreich, S. Micali and A. Wigderson, "Proofs that Yield Nothing but Their Validity or All Languages in NP Have Zero-Knowledge Proof Systems", Journal of the ACM 38(3), 1991: Section 3.1, the analysis following the physical implementation of Protocol 4 (rejection probability at least $1/m$ per round for $m = |E|$, acceptance of all $m^2$ rounds at most $(1 - m^{-1})^{m^2} \approx \exp(-m)$) and the proof of Proposition 4 (the same argument for Protocol 4, using unique decryption).
- O. Goldreich, "Foundations of Cryptography, Volume 1: Basic Tools", Cambridge University Press, 2001: Section 4.4.2, the proof of the proposition following Construction 4.4.7 (perfect completeness and rejection probability at least $1/|E|$, from the unambiguity of the commitment).
- M. Naor, "Bit Commitment Using Pseudorandomness", Journal of Cryptology 4(2), 1991 (at most $2^{2n}$ of the $2^{3n}$ strings $R$ allow a commitment with two openings).
