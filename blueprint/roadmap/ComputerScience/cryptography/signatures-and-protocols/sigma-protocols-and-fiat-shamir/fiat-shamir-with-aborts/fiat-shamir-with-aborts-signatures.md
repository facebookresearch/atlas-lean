# Fiat–Shamir with aborts signatures

Let $\Pi$ be a Sigma protocol with aborts for a relation $\mathcal{R}$ and let $H$ be a hash function (random oracle) into the challenge set. The *Fiat–Shamir with aborts* signature with attempt budget $K$ signs a message $m$ under witness $w$ by repeating, for $k = 1, \dots, K$: compute a commitment $t$ and state, set $c = H(m, t)$, and compute the response; the first non-aborting attempt yields the signature $(c, z)$ (or $(t, z)$). If all $K$ attempts abort, signing fails. Verification recomputes the commitment from $(c, z)$ and the statement (or checks $c = H(m, t)$) and runs the verifier of $\Pi$. In the random oracle analysis all $K$ attempts are executed and queried to the shared oracle, even after the first success, so that aborted commitments are also recorded.

## Depends on

- [Sigma protocols with aborts](sigma-protocols-with-aborts.md)
- [The random oracle model](../../../public-key/random-oracle-constructions/the-random-oracle-model.md)
- [Signature scheme](../../../security-games/generic-security-games/sig-scheme.md)

## Sources

- Vadim Lyubashevsky, "Fiat-Shamir with Aborts: Applications to Lattice and Factoring-Based Signatures", Advances in Cryptology – ASIACRYPT 2009, 2009.
- Vadim Lyubashevsky, "Lattice Signatures without Trapdoors", Advances in Cryptology – EUROCRYPT 2012, 2012.
- Manuel Barbosa et al., "Fixing and Mechanizing the Security Proof of Fiat-Shamir with Aborts and Dilithium", Cryptology ePrint Archive, Paper 2023/246, 2023.
