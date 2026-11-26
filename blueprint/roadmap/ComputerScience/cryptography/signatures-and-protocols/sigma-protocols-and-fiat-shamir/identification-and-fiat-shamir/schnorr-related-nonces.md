# Schnorr signatures with related nonces leak the signing key

In Schnorr's scheme over a group of prime order $q$ with generator $g$ and key $u = \alpha g$, a signature on $m$ with nonce $r$ is $(t, z) = (r g, r + c\alpha)$ with $c = H(m, t)$. If two messages $m_0 \ne m_1$ are signed with nonces $r$ and $a r + b$ for known $a, b \in \mathbb{Z}_q$, with challenges $c_0, c_1$ satisfying $a c_0 \ne c_1$, then

$$
\alpha = \frac{z_1 - a z_0 - b}{c_1 - a c_0},
$$

so the signing key is recovered from the two signatures. More generally, from two accepting conversations for $u$ whose commitments satisfy $t_1 = a t_0 + b g$, a witness can be extracted.

## Proof sketch

$z_1 - a z_0 = (a r + b + c_1 \alpha) - a(r + c_0 \alpha) = b + (c_1 - a c_0)\alpha$.

## Depends on

- [Fiat–Shamir signatures from Sigma protocols are EUF-CMA secure in the random oracle model](fiat-shamir-signatures.md)
- [The Schnorr identification protocol as a Sigma protocol](../../zero-knowledge-proofs/schnorr-sigma-protocol.md)

## Sources

- Dan Boneh and Victor Shoup, "A Graduate Course in Applied Cryptography", Version 0.6, 2023.
- Claus-Peter Schnorr, "Efficient Signature Generation by Smart Cards", Journal of Cryptology, 1991.
