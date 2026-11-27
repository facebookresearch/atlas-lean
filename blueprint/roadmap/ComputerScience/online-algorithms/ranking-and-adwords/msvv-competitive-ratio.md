# The MSVV tradeoff algorithm is (1 - 1/e)-competitive for small bids

The **MSVV algorithm** assigns each query $t$ to a bidder maximizing $b_{tj}\, \psi(f_j)$, where $f_j$ is the fraction of $j$'s budget already spent and $\psi(f) = 1 - e^{f-1}$. For bid ratio $R \ge 0$ and every feasible fractional solution $x$:

1. in the truncated-spend model, revenue $\ge (1 - e^{-1})\, e^{-R} \sum_{t,j} b_{tj} x_{tj}$;
2. in the all-or-nothing model with $0 \le R \le 1$, revenue $\ge (1 - e^{-1})(1 - R)\, e^{-R} \sum_{t,j} b_{tj} x_{tj}$.

As $R \to 0$ the ratio tends to $1 - 1/e$. No assumption that the offline optimum exhausts budgets is needed.

## Proof sketch

Primal-dual: when $t$ is assigned to $j$, set $\beta_t = b_{tj}\psi(f_j)$ and raise $\alpha_j$ so that $B_j \alpha_j$ grows by $b_{tj}(1 - \psi(f_j))$ up to discretization error controlled by $R$; the tradeoff function makes the dual feasible and the dual objective at most the revenue divided by $(1 - 1/e)e^{-R}$.

## Depends on

- [The AdWords (online budgeted allocation) problem and its LP relaxation](adwords-problem-and-lp.md)

## Proof depends on

- [Greedy is 1/2-competitive for AdWords](adwords-greedy-half-competitive.md)

## Sources

- A. Mehta, A. Saberi, U. Vazirani and V. Vazirani, "AdWords and Generalized Online Matching", Journal of the ACM 54(5), 2007.
- S. Lahaie, D. M. Pennock, A. Saberi and R. V. Vohra, "Sponsored Search Auctions", in N. Nisan, T. Roughgarden, É. Tardos and V. V. Vazirani (eds.), Algorithmic Game Theory, Cambridge University Press, 2007.
