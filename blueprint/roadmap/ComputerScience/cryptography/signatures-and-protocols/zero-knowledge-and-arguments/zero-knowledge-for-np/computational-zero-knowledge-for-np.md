# Every NP language has a computational zero-knowledge proof

Assume pseudorandom generators secure against nonuniform polynomial-size distinguishers exist. For every NP language $L$, fix a polynomial-time reduction $t$ from $L$ to graph 3-colorability together with a polynomial-time map from NP witnesses of $x$ to proper 3-colorings of $t(x)$ (Cook's reduction to 3SAT followed by the standard reduction from 3SAT to graph 3-colorability). On input $x$ with $t(x) = (V, E)$, the prover and the verifier run $|E|^2$ sequential executions of the graph 3-coloring protocol with Naor commitments on $t(x)$, each with fresh coins. This is an auxiliary-input computational zero-knowledge interactive proof for $L$ whose prover runs in probabilistic polynomial time given an NP witness: it is perfectly complete, has negligible soundness error against unbounded provers, and for every probabilistic polynomial-time verifier $V^*$ there is a probabilistic polynomial-time simulator whose output is computationally indistinguishable from the view of $V^*$ interacting with the honest prover, for every instance, witness and auxiliary input.

## Proof sketch

Completeness and soundness follow from the single-execution bounds, since $t$ maps members of $L$ to 3-colorable graphs and non-members to graphs that are not 3-colorable. For one execution, the simulator commits to colors $e_v \in \{1, 2, 3\}$ chosen uniformly and independently, runs $V^*$, and completes the view if $V^*$ asks for an edge with $e_u \ne e_v$; otherwise it retries. Hiding holds for every string $R$ the verifier sends, so the edge $V^*$ asks for is almost independent of the committed values, each attempt succeeds with probability close to $2/3$, and the completed views are indistinguishable from real ones; nonuniform security is needed because the instances on which simulation would fail are built into the distinguishing circuits. Sequential composition of auxiliary-input zero knowledge extends this to the $|E|^2$ executions, and stopping the retries after polynomially many attempts keeps the simulator strictly polynomial time.

## Depends on

- [The graph 3-coloring zero-knowledge protocol with Naor commitments](masked-3sat-zero-knowledge-protocol.md)
- [Zero-knowledge interactive proofs](../zero-knowledge-interactive-proofs.md)

## Proof depends on

- [Completeness and soundness of the graph 3-coloring protocol with Naor commitments](masked-3sat-completeness-soundness.md)
- [Naor's commitment is computationally hiding and statistically binding](../../commitment-schemes/commitments-and-zero-knowledge-for-np/naor-commitment-security.md)
- [Auxiliary-input computational zero knowledge](../../commitment-schemes/commitments-and-zero-knowledge-for-np/auxiliary-input-zero-knowledge.md)

## Sources

- O. Goldreich, S. Micali and A. Wigderson, "Proofs that Yield Nothing but Their Validity or All Languages in NP Have Zero-Knowledge Proof Systems", Journal of the ACM 38(3), 1991: Proposition 4 (Protocol 4 is a zero-knowledge proof for graph 3-colorability), Remark 16 (strictly polynomial-time simulation), Section 3.2, Theorem 5 (every language in NP has a zero-knowledge proof, via the reduction to graph 3-colorability) and Theorem 6 (probabilistic polynomial-time prover given an NP witness).
- O. Goldreich, "Foundations of Cryptography, Volume 1: Basic Tools", Cambridge University Press, 2001: Section 4.3.4 (sequential composition), Section 4.4.2 (Construction 4.4.7 and the proposition following it) and Section 4.4.3 (the general result for NP).
- M. Naor, "Bit Commitment Using Pseudorandomness", Journal of Cryptology 4(2), 1991.
