# Multiplicative ElGamal is semantically secure if and only if DDH holds

Over a decodable prime-order group family with a deterministic polynomial-time group schedule, multiplicative ElGamal (public key $u = g^{\alpha}$, ciphertext $(g^{\beta}, u^{\beta} m)$ for a group element $m$) is semantically secure (IND-CPA) if and only if DDH holds for that schedule. Moreover, for every DDH distinguisher there is a CPA adversary whose advantage is at least half the DDH advantage.

## Proof sketch

The forward direction is the standard reduction. Conversely, from a DDH distinguisher $D$ build a CPA adversary that, on public key $u$, submits $m_0 = 1$ and a uniform $m_1$, receives $(v, e)$, and outputs $D(u, v, e)$. If $b = 0$ then $(u, v, e)$ is a uniform Diffie–Hellman triple; if $b = 1$ then $e$ is uniform and independent, so $(u, v, e)$ is a uniform triple.

## Depends on

- [ElGamal as a public-key encryption scheme](../../cpa-security-of-elgamal/scheme.md)
- [Advantage of a DDH distinguisher](../ddh-advantage.md)
- [Cyclic and prime-order group families](../../discrete-logarithm-and-diffie-hellman-problems/diffie-hellman-problem-variants-and-attacks/cyclic-group-families.md)

## Proof depends on

- [ElGamal is CPA-secure if DDH is hard](../../cpa-security-of-elgamal/cpa-advantage-eq-ddh-advantage.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
- T. ElGamal, "A Public Key Cryptosystem and a Signature Scheme Based on Discrete Logarithms", IEEE Transactions on Information Theory 31(4), 1985.
