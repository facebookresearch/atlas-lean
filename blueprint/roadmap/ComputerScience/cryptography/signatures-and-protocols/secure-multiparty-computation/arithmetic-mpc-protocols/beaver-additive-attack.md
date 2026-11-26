# Additive attacks on Beaver-triple openings

In Beaver's multiplication over $\mathbb{Z}_p$, if a corrupted party adds $\delta_d$ to its share of the opened value $d = x - a$ and $\delta_e$ to its share of $e = y - b$, the honest parties' reconstructed output becomes

$$
xy + \delta_d\, y + \delta_e\, x + \delta_d\delta_e ,
$$

an affine error determined by the adversary's shifts and the secret inputs; in particular with $\delta_e = 0$ the product is shifted by exactly $\delta_d\, y$. Hence Beaver multiplication with unauthenticated shares is secure only against semi-honest adversaries, and authenticating shares with MACs (as in SPDZ) is needed to detect tampered openings.

## Proof sketch

Substitute $d + \delta_d$ and $e + \delta_e$ for the opened values in $\sum_i z_i = c + d b + e a + d e$ and use $b + e = y$, $a + d = x$.

## Depends on

- [Beaver's multiplication with dealer triples is correct and perfectly private](beaver-multiplication-triples.md)

## Sources

- Donald Beaver, "Efficient Multiparty Protocols Using Circuit Randomization", Advances in Cryptology –- CRYPTO '91, 1992.
- Dan Boneh and Victor Shoup, "A Graduate Course in Applied Cryptography", Version 0.6, 2023.
