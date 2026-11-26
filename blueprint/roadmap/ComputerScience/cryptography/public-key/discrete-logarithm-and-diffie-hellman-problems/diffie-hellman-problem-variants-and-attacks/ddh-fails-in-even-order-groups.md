# DDH does not hold in the even-order group $\mathbb{Z}_p^*$

Let $p$ be an odd prime and $g$ a generator of $\mathbb{Z}_p^*$, a cyclic group of even order $p - 1$. An element $g^{x}$ is a quadratic residue iff $x$ is even, which is tested by $(g^{x})^{(p-1)/2} = 1$. The distinguisher that accepts $(g^a, g^b, w)$ iff [$w^{(p-1)/2} = 1$] equals [$(g^a)^{(p-1)/2} = 1$ or $(g^b)^{(p-1)/2} = 1$] accepts every Diffie–Hellman triple and a random triple with probability exactly $1/2$, so its DDH advantage is $1/2$; it runs in polynomial time. Hence DDH does not hold in $\mathbb{Z}_p^*$, although CDH is believed to.

## Proof sketch

The quadratic character of $g^{ab}$ is determined by those of $g^a$ and $g^b$: $ab$ is even iff $a$ or $b$ is even. For a random third element the parity of its exponent is an independent fair coin.

## Depends on

- [Cyclic and prime-order group families](cyclic-group-families.md)
- [Advantage of a DDH distinguisher](../../elgamal-encryption/ddh-advantage.md)

## Sources

- D. Boneh, "The Decision Diffie–Hellman Problem", Algorithmic Number Theory (ANTS-III), LNCS 1423, Springer, 1998, pp. 48–63, Section 1.1.
- J. Katz and Y. Lindell, "Introduction to Modern Cryptography", 3rd ed., CRC Press, 2020, Section 15.4.1 and Exercise 15.16.
