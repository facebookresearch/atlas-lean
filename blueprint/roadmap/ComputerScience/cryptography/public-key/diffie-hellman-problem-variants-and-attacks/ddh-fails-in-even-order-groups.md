# DDH does not hold in cyclic groups of even order

In a cyclic group of even order $q$, an element $g^{x}$ is a square iff $x$ is even, which is tested by $(g^{x})^{q/2} = 1$. The distinguisher that accepts $(g^a, g^b, w)$ iff [$w^{q/2} = 1$] equals [$(g^a)^{q/2} = 1$ or $(g^b)^{q/2} = 1$] accepts every Diffie–Hellman triple and a random triple with probability exactly $1/2$, so its DDH advantage is $1/2$; it runs in polynomial time.

## Proof sketch

$ab$ is even iff $a$ or $b$ is even; for a random third element the parity of its exponent is an independent fair coin.

## Depends on

- [Cyclic and prime-order group families](cyclic-group-families.md)
- [Advantage of a DDH distinguisher](../elgamal-encryption/ddh-advantage.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
