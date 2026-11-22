# Price of anarchy 5/2 for affine congestion games

In a congestion game with affine delays $d_e(n) = a_e n + b_e$, $a_e, b_e \ge 0$, every pure Nash
equilibrium $s$ satisfies $C(s) \le \tfrac52\, C(t)$ for every profile $t$. The bound $5/2$ is
tight.

The proof is Roughgarden's three-line smoothness argument:
$C(s) \le \sum_i c_i(t_i, s_{-i}) \le \tfrac53 C(t) + \tfrac13 C(s)$.

## Informally uses

- [Affine congestion games are (5/3, 1/3)-smooth](is-smooth-of-affine.md).

## Background

- [Price of anarchy 4/3 for affine latencies](../selfish-routing-and-the-price-of-anarchy/cost-le-of-affine.md):
  the nonatomic counterpart, where each player is infinitesimal and the bound drops to $4/3$.

## Sources

- G. Christodoulou and E. Koutsoupias, "The price of anarchy of finite congestion games", STOC 2005, 67–73, Theorem 1.
- B. Awerbuch, Y. Azar and A. Epstein, "The price of routing unsplittable flow", STOC 2005, 57–66.
