# Multi-DDH from DDH

In a prime-order group family satisfying DDH, for polynomial counts $s(n)$ and $p(n)$, the distribution

$$\bigl(g^{\alpha_i},\ (g^{\beta_{ij}},\ g^{\alpha_i\beta_{ij}})_{j \le p}\bigr)_{i \le s}$$

with all exponents uniform is computationally indistinguishable from the same with each $g^{\alpha_i\beta_{ij}}$ replaced by an independent uniform $g^{\gamma_{ij}}$. A distinguisher's advantage is at most $s(n)$ times a DDH advantage plus $s(n)/q$.

## Proof sketch

Hybrid over the secrets $i$. For a fixed $i$, a single DDH triple $(u, v, w)$ is expanded into $p$ triples sharing first coordinate $u$ by rerandomization: real triples become independent real triples, random triples become independent random pairs.

## Depends on

- [Advantage of a DDH distinguisher](../../elgamal-encryption/ddh-advantage.md)

## Proof depends on

- [Rerandomization of DDH triples with a fixed first coordinate](ddh-triple-rerandomization.md)
- [Hybrid argument](../../../security-games/games-and-advantages/advantage-le-sum.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
- M. Naor and O. Reingold, "Number-Theoretic Constructions of Efficient Pseudo-Random Functions", Journal of the ACM 51(2), 2004.
