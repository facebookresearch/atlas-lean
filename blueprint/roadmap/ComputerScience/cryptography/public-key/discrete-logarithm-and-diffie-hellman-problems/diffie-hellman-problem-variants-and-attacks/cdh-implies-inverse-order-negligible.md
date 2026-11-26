# Under CDH the inverse group order is negligible

Let $d(n)$ be a deterministic schedule of prime-order groups with orders $q(d(n))$. If CDH holds for the point-mass setup at $d(n)$, then $1/q(d(n))$ is negligible in $n$. The same holds under DDH and under the discrete-logarithm assumption.

## Proof sketch

The adversary that outputs $g^{\gamma}$ for a uniform $\gamma$ (or the generator itself) wins CDH with probability at least $1/q$; under CDH this must be negligible.

## Depends on

- [Cyclic and prime-order group families](cyclic-group-families.md)
- [Computational Diffie–Hellman experiment](../../hardness-assumptions/cdh-game.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
