# Zero knowledge transfers along Levin reductions

Let $(f, g, h)$ be a Levin reduction from an NP relation $R$ to an NP relation $R'$: $f$ maps instances, $g$ maps witnesses of $x$ to witnesses of $f(x)$, and $h$ maps witnesses of $f(x)$ back to witnesses of $x$, all in polynomial time. If $R'$ has an auxiliary-input zero-knowledge proof with an efficient prover, then so does $R$: run the proof for $f(x)$ with witness $g(x, y)$. Soundness and zero knowledge transfer because $x \in L_R \iff f(x) \in L_{R'}$ and the simulator for $f(x)$ serves for $x$.

## Proof sketch

Completeness uses $g$; soundness uses that $f$ maps non-members to non-members; a cheating verifier for $x$ is a cheating verifier for $f(x)$, so its view is simulated by the simulator for $f(x)$ with the same auxiliary input.

## Depends on

- [Auxiliary-input computational zero knowledge](auxiliary-input-zero-knowledge.md)
- [The complexity class NP](../../../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/np.md)

## Sources

- O. Goldreich, "Foundations of Cryptography, Volume 1: Basic Tools", Cambridge University Press, 2001.
- O. Goldreich, S. Micali and A. Wigderson, "Proofs that Yield Nothing but Their Validity or All Languages in NP Have Zero-Knowledge Proof Systems", Journal of the ACM 38(3), 1991.
