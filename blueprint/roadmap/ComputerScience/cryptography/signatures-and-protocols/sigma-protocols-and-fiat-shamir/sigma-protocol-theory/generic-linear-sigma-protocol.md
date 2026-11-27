# The generic linear Sigma protocol

Fix a prime $q$ and $\mathbb{Z}_q$-vector spaces $V, W$ (e.g. powers of a group of order $q$). For a $\mathbb{Z}_q$-linear map $\psi_y : V \to W$ depending on the statement and a target $w_y \in W$, the relation is $\mathcal{R} = \{(x, y) : \psi_y(x) = w_y\}$. The prover sends $t = \psi_y(r)$ for uniform $r \in V$; on challenge $c \in \mathbb{Z}_q$ it answers $z = r + c\,x$; the verifier checks $\psi_y(z) = t + c\, w_y$. Schnorr's protocol ($\psi(x) = x g$), Okamoto's protocol ($\psi(x_1, x_2) = x_1 g + x_2 h$), and the Chaum–Pedersen protocol for equal discrete logarithms ($\psi(x) = (x g, x h)$) are instances.

## Depends on

- [A Sigma protocol](../../zero-knowledge-proofs/sigma-protocol.md)
- [The Schnorr identification protocol as a Sigma protocol](../../zero-knowledge-proofs/schnorr-sigma-protocol.md)

## Sources

- Dan Boneh and Victor Shoup, "A Graduate Course in Applied Cryptography", Version 0.6, 2023.
- Claus-Peter Schnorr, "Efficient Signature Generation by Smart Cards", Journal of Cryptology, 1991.
