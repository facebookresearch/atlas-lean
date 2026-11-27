# Datta's three-player Horner-chain game

Let $F_1, \dots, F_r$ be real polynomials in $n$ variables. Write each $F_j$ via Horner chains: a sequence of intermediate polynomials in which every step multiplies the previous value by one variable and adds a constant, so that each step is a single block-affine equation. *Datta's Horner-chain game* is the finite three-player game whose first player's strategies correspond to the variables (plus a slack strategy), whose second player's strategies correspond to the intermediate Horner values (rescaled into the open simplex), and whose third player's strategies enforce the chain equations; its costs are produced by block-affine realization so that the indifference equations of each player are exactly the Horner-chain equations.

## Depends on

- [Any block-affine polynomials are realized as expected pure-strategy costs](any-block-affine-polynomials-are-realized-as-expected-pure-strategy-costs.md)

## Sources

- Ruchira S. Datta, "Universality of Nash Equilibria", Mathematics of Operations Research, 2003.
