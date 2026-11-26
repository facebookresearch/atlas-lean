# Strong RSA assumption

A *group of unknown order* generator samples a finite abelian group $G$ (for instance $\mathbb{Z}_N^*$ for an RSA modulus $N$) and an element $g$. The *strong RSA assumption* states that every efficient adversary given $(G, g)$ outputs a pair $(x, e)$ with $x \in G$, $e \in \mathbb{Z}$, $e \ne \pm 1$ and $x^{e} = g$ only with negligible probability. Unlike the RSA assumption, the adversary chooses the exponent.

## Depends on

- [RSA-inversion experiment](../../hardness-assumptions/rsa-game.md)

## Sources

- N. Barić and B. Pfitzmann, "Collision-Free Accumulators and Fail-Stop Signature Schemes Without Trees", Advances in Cryptology (EUROCRYPT 1997), LNCS 1233, 1997.
- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
