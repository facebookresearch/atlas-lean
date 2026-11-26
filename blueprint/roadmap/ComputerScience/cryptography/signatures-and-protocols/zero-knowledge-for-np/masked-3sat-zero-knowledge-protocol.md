# The three-copy masked 3SAT zero-knowledge protocol

Let $f$ map instances of an NP language to 3CNF formulas and let $G$ be a pseudorandom generator with stretch $\ell(m) \ge 3m + 1$, used for Naor-style bit commitments. To prove that $\varphi = f(a)$ is satisfiable with witness $w$, the prover prepares three independently masked copies of a satisfying assignment and the clause evaluations in which every value is XOR-masked, commits to all masked values with PRG-based commitments under the verifier's first-message randomness, and sends the commitments. The verifier picks a random clause and a random one of three consistency checks; the prover opens exactly the commitments the check requires, which reveal only uniformly masked bits consistent with the chosen clause being satisfied. The verifier accepts iff the openings verify and are consistent.

## Depends on

- [Zero-knowledge interactive proofs](../zero-knowledge-and-arguments/zero-knowledge-interactive-proofs.md)
- [CPA security of public-key encryption families](../../security-games/asymptotic-security/pub-cpasecure.md)

## Sources

- Oded Goldreich, Silvio Micali and Avi Wigderson, "Proofs that Yield Nothing but Their Validity or All Languages in NP Have Zero-Knowledge Proof Systems", Journal of the ACM, 1991.
- Oded Goldreich, "Foundations of Cryptography, Volume 2: Basic Applications", Cambridge University Press, 2004.
