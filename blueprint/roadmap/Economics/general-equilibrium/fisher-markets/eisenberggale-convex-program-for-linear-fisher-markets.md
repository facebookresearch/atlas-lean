# Eisenberg–Gale convex program for linear Fisher markets

Let a [linear Fisher market](linear-fisher-markets.md) be given, with buyers $i \in B$, goods $j \in A$, budgets $e_i > 0$ and utilities $u_i(x) = \sum_j u_{ij} x_{ij}$, and with *market equilibrium* in the sense of that page: each buyer's bundle maximizes her utility among bundles of cost at most $e_i$, and every good with positive price is fully sold. At an equilibrium all prices are positive, since a free good valued by some buyer would be demanded without bound; so the bang per buck $u_{ij}/p_j$ is defined, and an equilibrium is equivalently characterized by: every good is fully sold, each buyer receives only goods maximizing $u_{ij}/p_j$, and each buyer spends all her money.

Consider the Eisenberg–Gale convex program:

$$
\text{maximize } \sum_{i \in B} e_i \log u_i \quad\text{subject to}\quad u_i = \sum_{j} u_{ij} x_{ij}, \quad \sum_{i} x_{ij} \le 1, \quad x_{ij} \ge 0.
$$

**Theorem.**
1. If $x$ is optimal and $p$ are the optimal Lagrange multipliers of the constraints $\sum_i x_{ij} \le 1$, then $(p, x)$ is a market equilibrium. In particular, an equilibrium exists, all prices are positive and all goods are fully sold.
2. Conversely, every equilibrium allocation is an optimal solution. Hence the set of equilibrium allocations is convex.
3. Equilibrium utilities and equilibrium prices are unique.

**Proof.** The program is feasible with finite optimum, because every buyer values some good. Write it as minimizing the convex function $-\sum_i e_i \log u_i$ over the convex domain where every $u_i > 0$. The point $x_{ij} = 1/(2|B|)$ satisfies every constraint $\sum_i x_{ij} \le 1$ strictly and has $u_i > 0$ for every buyer, so Slater's condition holds and optimal Lagrange multipliers $p$ exist. At an optimum the Karush–Kuhn–Tucker conditions read:
- $p_j \ge 0$, and $p_j > 0$ implies that good $j$ is fully sold;
- $p_j \ge e_i u_{ij}/u_i$ for all $i, j$, with equality when $x_{ij} > 0$.

Equality gives $p_j x_{ij} = e_i u_{ij} x_{ij}/u_i$, and summing over $j$ gives $\sum_j p_j x_{ij} = e_i$. A good valued by buyer $i$ has $p_j \ge e_i u_{ij}/u_i > 0$, so it is fully sold. This proves part 1.

For part 2, an equilibrium $(p, x)$ satisfies these conditions, because all prices are positive and $u_i/e_i$ equals buyer $i$'s maximal bang per buck $\max_j u_{ij}/p_j$. The KKT conditions are sufficient for a concave program, so $x$ is optimal.

For part 3, $\log$ is strictly concave, so all optimal solutions have the same utilities $u_i$. Every good is bought by some buyer, so the equality condition then determines $p_j$.

## Depends on

- [Linear Fisher markets](linear-fisher-markets.md)

## Proof depends on

- [Slater's theorem, multiplier form](../../../Analysis/convex-analysis-and-variations/lagrange-duality/exists-multiplier-of-slater.md)
- [Sufficiency of the KKT conditions for convex problems](../../../Analysis/convex-analysis-and-variations/lagrange-duality/kkt-sufficient.md)

## Sources

- V. V. Vazirani, "Combinatorial algorithms for market equilibria", Chapter 5 of N. Nisan, T. Roughgarden, É. Tardos and V. V. Vazirani (eds.), *Algorithmic Game Theory*, Cambridge University Press, 2007, <https://www.cs.cmu.edu/~sandholm/cs15-892F13/algorithmic-game-theory.pdf>:
    - Section 5.2 (Fisher's linear case, the Eisenberg–Gale program (5.1) and its KKT conditions (i)–(iv));
    - Theorem 5.1 and its proof (existence, convexity of the set of equilibrium allocations, uniqueness of equilibrium utilities and prices).
- D. Chakrabarty, N. Devanur and V. V. Vazirani, "Rationality and strongly polynomial solvability of Eisenberg–Gale markets with two agents", <https://www-dev.ics.uci.edu/~vazirani/EG2.pdf>, Section 2.1: the market equilibrium conditions (1)–(3), program (4), and Theorem 2.1 with its KKT proof.
- E. Eisenberg and D. Gale, "Consensus of subjective probabilities: the pari-mutuel method", *Annals of Mathematical Statistics* 30(1):165–168, 1959.
