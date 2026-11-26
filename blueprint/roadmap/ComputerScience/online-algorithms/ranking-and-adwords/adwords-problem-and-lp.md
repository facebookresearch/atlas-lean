# The AdWords (online budgeted allocation) problem and its LP relaxation

In the **AdWords problem**, bidders $j$ have budgets $B_j > 0$; queries $t = 1, 2, \dots$ arrive online, query $t$ revealing bids $b_{tj} \ge 0$, and each query must be assigned irrevocably to at most one bidder. In the **truncated-spend** model a bidder pays $\min(b_{tj}, \text{remaining budget})$; in the **all-or-nothing** model a query is assigned to $j$ only if the full bid fits in the remaining budget. Revenue is the total payment. The offline **fractional relaxation** is

$$
\max \sum_{t,j} b_{tj}\, x_{tj} \quad \text{s.t.} \quad \sum_t b_{tj} x_{tj} \le B_j \ \forall j, \quad \sum_j x_{tj} \le 1 \ \forall t, \quad x \ge 0,
$$

whose dual minimizes $\sum_j B_j \alpha_j + \sum_t \beta_t$ subject to $\beta_t \ge b_{tj}(1 - \alpha_j)$, $\alpha, \beta \ge 0$. Weak duality and complementary slackness hold. The **bid ratio** is the least $R$ with $b_{tj} \le R\, B_j$ for all $t, j$.

## Depends on

- [Deterministic online bipartite matching algorithm](../online-bipartite-matching/online-matcher.md)

## Sources

- A. Mehta, A. Saberi, U. Vazirani and V. Vazirani, "AdWords and Generalized Online Matching", Journal of the ACM 54(5), 2007.
- S. Lahaie, D. M. Pennock, A. Saberi and R. V. Vohra, "Sponsored Search Auctions", in N. Nisan, T. Roughgarden, É. Tardos and V. V. Vazirani (eds.), Algorithmic Game Theory, Cambridge University Press, 2007.
