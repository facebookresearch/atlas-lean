# Under CDH, no efficient adversary lists the Diffie–Hellman value among polynomially many candidates

In a prime-order group family satisfying CDH, every probabilistic polynomial-time adversary that receives $(g, g^\alpha, g^\beta)$ and outputs a list of at most $\ell(n)$ group elements (any polynomial $\ell$) includes $g^{\alpha\beta}$ in the list only with negligible probability.

## Proof sketch

The CDH adversary runs the list adversary and outputs a uniformly random element of the list, losing a factor of at most $\ell(n)$.

## Depends on

- [Computational Diffie–Hellman experiment](../../hardness-assumptions/cdh-game.md)

## Sources

- D. Cash, E. Kiltz and V. Shoup, "The Twin Diffie–Hellman Problem and Applications", Journal of Cryptology 22(4), 2009, pp. 470–504.
