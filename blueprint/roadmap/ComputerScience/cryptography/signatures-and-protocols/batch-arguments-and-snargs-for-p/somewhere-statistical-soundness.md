# Somewhere statistical soundness of arguments

Consider a public-coin four-message interactive argument $(P,V)$ for a language $L$ in which the verifier sends the first and third messages. It is *somewhere statistically sound (SSS)* with respect to a decisional complexity assumption $A$ if for every first verifier message $\beta_1$ there is a third verifier message $T(\beta_1)$, possibly not efficiently computable, such that: (i) *somewhere statistical soundness:* for every polynomial-size cheating prover $P^{*}$ that outputs an instance $x$ together with its second message, conditioned on the first three messages being $(\beta_1,P^{*}(\beta_1),T(\beta_1))$, the remaining protocol is statistically sound for $x\notin L$, even against unbounded provers, with overwhelming probability over $\beta_1$, assuming $A$; and (ii) *computational indistinguishability:* the pair $(\beta_1,T(\beta_1))$ is computationally indistinguishable from a pair of independent uniform verifier messages $(\beta_1,\beta_2)$. Both properties are required to hold through straight-line (non-rewinding) reductions to $A$. The name is by analogy with somewhere statistical binding: an instantiation of Kilian's protocol with a multi-extractable SSB hash is SSS when the verifier's PCP queries point to the positions the hash binds statistically. SSS arguments allow soundness proofs that first move to the special third message and then argue information-theoretically, which also makes them post-quantum sound when the assumption is.

## Depends on

- [Interactive arguments](../zero-knowledge-and-arguments/interactive-arguments.md)
- [Somewhere extractable (somewhere statistically binding) hash functions](somewhere-extractable-hash.md)

## Sources

- Yael Tauman Kalai, Vinod Vaikuntanathan, Rachel Yun Zhang, "Somewhere Statistical Soundness, Post-Quantum Security, and SNARGs", TCC (2021), Section 1.2 and Definition 4.2.
