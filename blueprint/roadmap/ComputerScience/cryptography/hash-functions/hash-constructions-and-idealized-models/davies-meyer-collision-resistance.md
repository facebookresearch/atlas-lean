# Davies–Meyer is collision resistant in the ideal cipher model

In the ideal cipher model on a finite block set $X$, every randomized adaptive collision finder making at most $Q$ forward or inverse ideal-cipher queries outputs two distinct inputs $(k, x) \ne (k', x')$ with $h_{\mathrm{DM}}(k, x) = h_{\mathrm{DM}}(k', x')$ with probability at most

$$\frac{(Q+1)(Q+2)}{|X|}.$$

## Proof sketch

Each query determines a triple $(k, x, E(k,x))$ whose Davies–Meyer value is uniform over at least $|X| - i$ values when the $i$-th query is answered; a collision requires one triple's value to hit an earlier one. Adding the two evaluations of the output and summing over pairs gives the bound.

## Depends on

- [Davies–Meyer compression function](davies-meyer-compression.md)

## Proof depends on

- [Triangular (birthday-type) bound for linearly growing bad sets](../../security-games/identical-until-bad-oracle-handlers/triangular-bad-event-bound.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
- J. Black, P. Rogaway and T. Shrimpton, "Black-Box Analysis of the Block-Cipher-Based Hash-Function Constructions from PGV", Advances in Cryptology (CRYPTO 2002), LNCS 2442, 2002.
