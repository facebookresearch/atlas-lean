# SPDZ authenticated secret sharing

Let $p$ be prime and $\alpha \in \mathbb{F}_p$ a global MAC key additively shared as $\alpha = \sum_i \alpha_i$. A value $x$ is *authenticated-shared*, written $\langle x\rangle$, when party $i$ holds $x_i$ and $\gamma_i$ with $\sum_i x_i = x$ and $\sum_i \gamma_i = \alpha x$. Linear operations act share-wise: $\langle x \rangle + \langle y \rangle$, $c\langle x \rangle$, and adding a public constant $c$ (one party adds $c$ to its share and every party adds $c\,\alpha_i$ to its MAC share). Multiplication uses authenticated Beaver triples $(\langle a\rangle, \langle b\rangle, \langle c\rangle)$ as in Beaver's protocol. Opened values are checked by *MACCheck*: after opening $x$, the parties commit to and then open $\sigma_i = \gamma_i - \alpha_i x$ and accept iff $\sum_i \sigma_i = 0$; for a batch of openings they check a random linear combination.

## Depends on

- [Beaver's multiplication with dealer triples is correct and perfectly private](beaver-multiplication-triples.md)

## Sources

- Ivan Damgaard, Valerio Pastro, Nigel P. Smart and Sarah Zakarias, "Multiparty Computation from Somewhat Homomorphic Encryption", Advances in Cryptology –- CRYPTO 2012, 2012.
- Ivan Damgaard et al., "Practical Covertly Secure MPC for Dishonest Majority –- Or: Breaking the SPDZ Limits", Computer Security –- ESORICS 2013, 2013.
