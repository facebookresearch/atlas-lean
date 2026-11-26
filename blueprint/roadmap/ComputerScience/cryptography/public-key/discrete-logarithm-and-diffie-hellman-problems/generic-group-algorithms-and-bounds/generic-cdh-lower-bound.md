# Generic lower bound for computational Diffie–Hellman

For prime $q$, every generic algorithm that receives $L(1), L(\alpha), L(\beta)$ for uniform $\alpha, \beta$ and makes at most $T$ group-oracle queries outputs the label $L(\alpha\beta)$ with probability at most

$$\frac{(3T + 4)^2/2 + 2}{q}.$$

## Proof sketch

Track labels as linear polynomials in two unknowns. A collision between distinct tracked polynomials, or between the output and the degree-two polynomial $XY$, occurs with probability at most $2/q$ per pair by the Schwartz–Zippel lemma, and there are at most $\binom{3T+4}{2}$ pairs.

## Depends on

- [Generic group oracle with labelings](generic-group-oracle.md)
- [Computational Diffie–Hellman experiment](../../hardness-assumptions/cdh-game.md)

## Proof depends on

- [Shoup's generic lower bound for discrete logarithms](../../hardness-assumptions/shoup-s-generic-lower-bound-for-discrete.md)
- [Fundamental lemma of game playing for stateful oracle handlers](../../../security-games/identical-until-bad-oracle-handlers/fundamental-lemma-for-stateful-handlers.md)

## Sources

- V. Shoup, "Lower Bounds for Discrete Logarithms and Related Problems", Advances in Cryptology (EUROCRYPT 1997), LNCS 1233, 1997.
- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
