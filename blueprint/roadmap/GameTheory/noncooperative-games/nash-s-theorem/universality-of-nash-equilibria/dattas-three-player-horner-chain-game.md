# Datta's three-player Horner-chain game

Let $F_1, \dots, F_r$ be real polynomials in $n$ variables, not all constant, whose common zeros all lie in the open simplex $\{x : x_i > 0 \text{ for all } i,\ \sum_i x_i < 1\}$, let $d_{ij}$ be the highest power of $x_i$ in $F_j$, and set $D = -1 + \sum_{j=1}^r \prod_{i=1}^n (1 + d_{ij})$. Expanding each $F_j$ by Horner's rule one variable at a time gives a chain of $D - r$ intermediate polynomials, each obtained from earlier ones (or from constants) by multiplying one of them by a variable and adding another or a constant; this yields $D$ equations, $D - r$ *chain equations* equating each intermediate value to the step that produces it and the $r$ final equations $F_j = 0$. *Datta's Horner-chain game* is the three-player game in which

- the first player has $n + 1$ pure strategies, whose weights $a_1, \dots, a_n$ play the role of $x_1, \dots, x_n$ (with slack weight $a_0 = 1 - \sum_i a_i$);
- the second player has $D - r + 1$ pure strategies, whose weights $b_1, \dots, b_{D-r}$ are fixed affine rescalings of the intermediate values (value $= s_k b_k + \delta_k$ with constants $s_k \ne 0$ and $\delta_k$ chosen so that $b_k > 0$ and $\sum_k b_k < 1$ at every common zero), with slack weight $b_0$;
- the third player has $D + 1$ pure strategies, with weights $c_0, \dots, c_D$.

Its costs are produced by block-affine realization so that the third player's $D$ indifference equations, which involve only the first two players' weights, are exactly the $D - r$ chain equations and the $r$ final equations, written in $a$ and the rescaled $b$. The first player's $n$ indifference equations and the second player's $D - r$ indifference equations involve the third player's weights; $\min(D, n + D - r)$ of them set distinct weights among $c_1, \dots, c_D$ equal to $1/(D + 1)$, and any remaining ones are trivial. (Datta pins these weights to $1/D$, which leaves $c_0 > 0$ only when $r > n$; the value $1/(D + 1)$ also covers $r \le n$.)

## Depends on

- [Any block-affine polynomials are realized as expected pure-strategy costs](any-block-affine-polynomials-are-realized-as-expected-pure-strategy-costs.md)

## Sources

- Ruchira S. Datta, "Universality of Nash Equilibria", Mathematics of Operations Research, 2003.
