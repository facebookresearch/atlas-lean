# Unforgeability of Lyubashevsky's Fiat–Shamir-with-aborts signatures under SIS

Consider the Fiat–Shamir-with-aborts signature built from Lyubashevsky's protocol with uniform $A \in \mathbb{Z}_q^{n\times m}$, uniform secret $S \in [-\eta, \eta]^{m \times k}$, $k$-bit challenges from a random oracle, and attempt budget $K$. Then: (i) for parameters with $k\eta \le \beta$ and $\gamma \ge 2m\beta$, each signing attempt aborts with probability at most $1/2$ even when the challenge is chosen by a hash of the commitment, so signing fails with probability at most $2^{-K}$; (ii) signing can be simulated without the secret key by programming the random oracle at simulated commitments, at a statistical cost bounded by the probability that a fresh commitment hits a previously queried point, summed over the $K q_S$ attempts; (iii) the joint law of signatures and hash cache is the same for all bounded secrets with the same public key; (iv) consequently every forger making $q_S$ signing and $q_H$ hash queries with success probability $\varepsilon$ yields, by forking, a nonzero homogeneous SIS solution $x$ for $A$ ($A x \equiv 0$) with norm bound $2(\gamma - \beta) + k\eta$ with probability at least $\varepsilon'^2/(q_H + K q_S) - \varepsilon'/2^k - k\, q^n / (2\eta + 1)^m$, where $\varepsilon'$ is $\varepsilon$ minus the simulation loss and the last term is the secret-prediction term. In particular, with $K \ge \lambda$ the signing failure is at most $2^{-\lambda}$, and for parameters polynomial in $\lambda$ that make $2^{-k}$, the simulation loss and the secret-prediction term negligible, SIS hardness at norm bound $2(\gamma - \beta) + k\eta$ makes the scheme EUF-CMA secure in the random oracle model.

## Proof sketch

Witness invariance of the full view lets the reduction choose its own secret. Forking at the hash query of the forgery gives two responses for distinct challenges and the same commitment, whose difference is a relaxed witness; it differs from the one obtained from the reduction's own secret unless the forger predicted the secret's response difference, which by the remaining min-entropy of $S$ given $AS$ has the stated probability.

## Depends on

- [Fiat–Shamir with aborts signatures](fiat-shamir-with-aborts-signatures.md)
- [Lyubashevsky's lattice identification protocol](lyubashevsky-identification.md)
- [Signature schemes and (strong) unforgeability in the random oracle model](../random-oracle-signatures/rom-signature-unforgeability.md)
- [The short integer solution problem (SIS)](../../../public-key/lattice-and-code-based-cryptography/lattice-problems/short-integer-solution-problem.md)

## Proof depends on

- [Completeness, abort probability and zero knowledge of Lyubashevsky's protocol](lyubashevsky-identification-properties.md)
- [Lyubashevsky identification is a proof of knowledge of short SIS solutions](lyubashevsky-proof-of-knowledge.md)
- [The general forking lemma](../random-oracle-signatures/general-forking-lemma.md)
- [Zero knowledge up to aborts](zero-knowledge-up-to-aborts.md)

## Sources

- Vadim Lyubashevsky, "Lattice Signatures without Trapdoors", Advances in Cryptology – EUROCRYPT 2012, 2012.
- Vadim Lyubashevsky, "Fiat-Shamir with Aborts: Applications to Lattice and Factoring-Based Signatures", Advances in Cryptology – ASIACRYPT 2009, 2009.
- Manuel Barbosa et al., "Fixing and Mechanizing the Security Proof of Fiat-Shamir with Aborts and Dilithium", Cryptology ePrint Archive, Paper 2023/246, 2023.
