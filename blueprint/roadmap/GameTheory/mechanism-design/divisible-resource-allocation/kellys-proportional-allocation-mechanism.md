# Kelly's proportional allocation mechanism

A divisible resource of capacity $C > 0$ is shared by users $i$ with concave, strictly increasing, differentiable utilities $U_i$ on $[0, \infty)$ (admissible utilities). Each user bids $w_i \ge 0$; the price is $\rho = \sum_j w_j / C$ and user $i$ receives $d_i = C w_i / \sum_j w_j$ (zero when all bids vanish), with payoff $U_i(d_i) - w_i$. Users are *price-taking* if they treat $\rho$ as fixed and *price-anticipating* if they account for their effect on $\rho$; a *social optimum* maximizes $\sum_i U_i(d_i)$ subject to $\sum_i d_i \le C$, $d \ge 0$.

## Depends on

- [Social welfare](../vickrey-clarke-groves-mechanisms/welfare.md)
- [Pure Nash equilibrium of a finite game](../../noncooperative-games/potential-games/is-pure-nash-2.md)

## Sources

- Ramesh Johari, "The Price of Anarchy and the Design of Scalable Resource Allocation Mechanisms", Algorithmic Game Theory, Cambridge University Press, 2007.
- Frank P. Kelly, "Charging and Rate Control for Elastic Traffic", European Transactions on Telecommunications, 1997.
