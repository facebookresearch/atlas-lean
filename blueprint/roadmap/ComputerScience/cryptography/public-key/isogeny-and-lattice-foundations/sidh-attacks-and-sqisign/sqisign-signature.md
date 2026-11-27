# SQIsign: compact signatures from the SQIsign identification protocol

Applying the Fiat–Shamir transform to the SQIsign identification protocol, with the challenge $\varphi$ derived by hashing the commitment $E_1$ and the message, yields a digital signature scheme (SQIsign) whose public keys and signatures consist of a constant number of elements of $\mathbb{F}_{p^{2}}$ plus short integers, i.e., $O(\lambda)$ bits each. The protocol is complete, and it is special sound with respect to the endomorphism ring problem: two accepting responses for the same commitment and distinct challenges give a non-trivial endomorphism of $E_A$.

## Proof sketch

Completeness follows from the correctness of the ideal-to-isogeny translation. For special soundness, two responses $\sigma,\sigma'$ to challenges $\varphi\ne\varphi'$ from the same $E_1$ give the endomorphism $\hat{\sigma}'\circ\varphi'\circ\hat{\varphi}\circ\sigma$ of $E_A$, which is non-scalar by the non-backtracking condition. Signature security follows from Fiat–Shamir in the random oracle model given soundness and a zero-knowledge (simulatability) property of responses.

## Depends on

- [The SQIsign identification protocol](sqisign-identification.md)
- [The random oracle model](../../random-oracle-constructions/the-random-oracle-model.md)

## Proof depends on

- [Security of the Fiat–Shamir transform](../../../signatures-and-protocols/zero-knowledge-and-arguments/security-of-the-fiatshamir-transform.md)

## Sources

- Luca De Feo, David Kohel, Antonin Leroux, Christophe Petit, Benjamin Wesolowski, "SQISign: Compact Post-Quantum Signatures from Quaternions and Isogenies", ASIACRYPT (2020), IACR ePrint 2020/1240.
