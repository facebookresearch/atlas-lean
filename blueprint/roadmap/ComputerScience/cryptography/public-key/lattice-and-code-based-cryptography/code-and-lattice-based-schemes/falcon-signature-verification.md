# Falcon (hash-and-sign NTRU lattice) signature verification

Let $q = 12289$, $\phi = X^{n} + 1$ and $\mathcal{R}_q = \mathbb{Z}_q[X]/(\phi)$, with public key $h = g f^{-1} \in \mathcal{R}_q$ for short secret polynomials $f, g$. A *Falcon* signature on $m$ consists of a salt $r$ and a short polynomial $s_2$; the verifier computes $c = H(r \| m) \in \mathcal{R}_q$, sets $s_1 = c - s_2 h \bmod q$ (centered), and accepts iff $\|(s_1, s_2)\|^2 \le \lfloor\beta^2\rfloor$ for a fixed bound $\beta$. Signing samples $(s_1, s_2)$ from a discrete Gaussian over the coset $\{(s_1, s_2) : s_1 + s_2 h = c\}$ using the secret trapdoor, following the GPV hash-and-sign paradigm.

## Depends on

- [Gaussian function, Gaussian mass and discrete Gaussian on a lattice](../lattice-gaussians-and-smoothing-parameter/discrete-gaussian-on-a-lattice.md)
- [Signature scheme](../../../security-games/generic-security-games/sig-scheme.md)

## Sources

- P.-A. Fouque, J. Hoffstein, P. Kirchner, V. Lyubashevsky, T. Pornin, T. Prest, T. Ricosset, G. Seiler, W. Whyte and Z. Zhang, "Falcon: Fast-Fourier Lattice-Based Compact Signatures over NTRU", specification v1.2, NIST post-quantum cryptography submission, 2020.
- C. Gentry, C. Peikert and V. Vaikuntanathan, "Trapdoors for Hard Lattices and New Cryptographic Constructions", Proceedings of the 40th Annual ACM Symposium on Theory of Computing (STOC), 2008.
