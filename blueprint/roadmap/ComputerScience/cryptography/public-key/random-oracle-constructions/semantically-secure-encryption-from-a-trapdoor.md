# Semantically secure encryption from a trapdoor function in the random oracle model

Let $(\mathrm{Gen}, F, I)$ be a one-way trapdoor function scheme on a set $X$, $\mathcal{E}_s$ a semantically secure symmetric cipher with key space $K$, and $H : X \to K$ a hash function modelled as a random oracle. The public-key scheme that encrypts $m$ by choosing a uniform $x \in X$ and outputting $(F(pk, x), \mathcal{E}_s(H(x), m))$ is semantically secure: for every adversary $A$ there are an inverter $B_{\mathrm{ow}}$ and an adversary $B_s$ against $\mathcal{E}_s$ with

$$\mathrm{Adv}^{\mathrm{SS}}[A] \le 2\cdot \mathrm{Adv}^{\mathrm{OW}}[B_{\mathrm{ow}}, F] + \mathrm{Adv}^{\mathrm{SS}}[B_s, \mathcal{E}_s].$$


Instantiated with RSA it is secure under the RSA assumption.

## Depends on

- [Trapdoor permutations](../hardness-assumptions/trapdoor-permutations.md)
- [The random oracle model](the-random-oracle-model.md)
- [Public-key encryption scheme](../../security-games/generic-security-games/pkescheme.md)
- [Private-key encryption scheme](../../security-games/generic-security-games/symm-enc-scheme.md)

## Sources

- D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*, version 0.4, 2017, <https://toc.cryptobook.us/>, Theorem 11.2
