# DDH fails when the group order has a small prime factor

Let $\ell$ be a prime divisor of the group order $q$. The test accepting $(g^a, g^b, w)$ iff [$w^{q/\ell} = 1$] equals [$(g^a)^{q/\ell} = 1$ or $(g^b)^{q/\ell} = 1$] has DDH advantage at least $1/\ell - 1/\ell^2 \ge 1/(2\ell)$. Hence if every group in the support of the setup has a prime factor of the order bounded by a polynomial $B(n)$ that can be found in polynomial time, DDH does not hold.

## Proof sketch

The test checks whether $ab \equiv 0 \pmod{\ell}$ agrees with $a \equiv 0$ or $b \equiv 0$, which always holds for real triples and fails for random triples with probability exactly $(1 - 1/\ell)(3/\ell - 2/\ell^2)$.

## Depends on

- [Cyclic and prime-order group families](cyclic-group-families.md)
- [Advantage of a DDH distinguisher](../../elgamal-encryption/ddh-advantage.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
- S. C. Pohlig and M. E. Hellman, "An Improved Algorithm for Computing Logarithms over GF(p) and Its Cryptographic Significance", IEEE Transactions on Information Theory 24(1), 1978.
