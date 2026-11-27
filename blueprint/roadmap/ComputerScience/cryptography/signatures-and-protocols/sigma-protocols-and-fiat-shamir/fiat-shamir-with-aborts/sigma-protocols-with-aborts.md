# Sigma protocols with aborts

A *Sigma protocol with aborts* for a relation $\mathcal{R}$ is a three-move protocol in which the prover sends a commitment $t$, receives a uniform challenge $c$ from a challenge set $C$, and replies with either a response $z$ or the abort symbol $\bot$. It is *complete up to aborts* if every non-aborting answer of the honest prover on a valid statement–witness pair is accepted. It is *non-abort special honest-verifier zero knowledge* if there is a simulator that, given the statement and a challenge $c$, outputs a pair $(t, z)$ or $\bot$ distributed exactly as the honest prover's *accepted view*: the prover's output on $c$ with commitments of aborted runs erased.

## Proof sketch

The accepted view determines the full transcript law, including the commitment of an aborted run, once the commitment marginal is known. The commitment $t$ is sent before the challenge, so its law $P(t)$ does not depend on $c$; for each challenge $c$ and commitment $t$, the accepted view gives $P(t, z \mid c)$ for every response $z$, and the aborted runs with commitment $t$ have probability $P(t, \bot \mid c) = P(t) - \sum_z P(t, z \mid c)$.

## Depends on

- [A Sigma protocol](../../zero-knowledge-proofs/sigma-protocol.md)
- [Perfect special honest-verifier zero knowledge](../../zero-knowledge-proofs/special-hvzk.md)

## Sources

- Vadim Lyubashevsky, "Fiat-Shamir with Aborts: Applications to Lattice and Factoring-Based Signatures", Advances in Cryptology – ASIACRYPT 2009, 2009.
- Vadim Lyubashevsky, "Lattice Signatures without Trapdoors", Advances in Cryptology – EUROCRYPT 2012, 2012.
- Manuel Barbosa et al., "Fixing and Mechanizing the Security Proof of Fiat-Shamir with Aborts and Dilithium", Cryptology ePrint Archive, Paper 2023/246, 2023.
