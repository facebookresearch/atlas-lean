# The MSVV tradeoff algorithm is (1 - 1/e)-competitive for small bids

The **MSVV algorithm** assigns each query $t$ to a bidder maximizing $b_{tj}\, \psi(f_j)$, where $f_j$ is the fraction of $j$'s budget already spent and $\psi(f) = 1 - e^{f-1}$. In the truncated-spend model it is $(1 - 1/e)$-competitive as the bid ratio tends to $0$: for every $\varepsilon > 0$ there is $R_0 > 0$ such that on every instance with bid ratio at most $R_0$ its revenue is at least $(1 - 1/e - \varepsilon) \sum_{t,j} b_{tj} x_{tj}$ for every feasible solution $x$ of the fractional relaxation. No assumption that the offline optimum exhausts budgets is needed.

## Proof sketch

Primal-dual: when $t$ is assigned to $j$, set $\beta_t = b_{tj}\psi(f_j)$ and raise $\alpha_j$ so that $B_j \alpha_j$ grows by $b_{tj}(1 - \psi(f_j))$ up to discretization error controlled by the bid ratio $R$; the tradeoff function makes the dual feasible and the dual objective at most the revenue divided by $(1 - 1/e)e^{-R}$. By weak duality this gives revenue at least $(1 - e^{-1})\, e^{-R} \sum_{t,j} b_{tj} x_{tj}$ for every bid ratio $R$, including the truncated last payment of each bidder, and $e^{-R} \to 1$ as $R \to 0$.

## Depends on

- [The AdWords (online budgeted allocation) problem and its LP relaxation](adwords-problem-and-lp.md)

## Proof depends on

- [Greedy is 1/2-competitive for AdWords](adwords-greedy-half-competitive.md)

## Sources

- A. Mehta, A. Saberi, U. Vazirani and V. Vazirani, "AdWords and Generalized Online Matching", Journal of the ACM 54(5), 2007: Theorem 8 (ratio $1 - 1/e$ as the discretization $k$ tends to infinity, under the assumption that each bid is small compared to its budget) and §6, items 1-2 (different budgets; an optimal allocation that does not exhaust all budgets). Author's copy: <https://people.eecs.berkeley.edu/~vazirani/pubs/adwords.pdf>
- S. Lahaie, D. M. Pennock, A. Saberi and R. V. Vohra, "Sponsored Search Auctions", in N. Nisan, T. Roughgarden, É. Tardos and V. V. Vazirani (eds.), Algorithmic Game Theory, Cambridge University Press, 2007.
- A. Mehta, "Online Matching and Ad Allocation", Foundations and Trends in Theoretical Computer Science 8(4), 2013, §6.1: Algorithm 11 (Primal-Dual Adwords), the remark that it is identical to MSVV with the tradeoff $1 - e^{x_u - 1}$, and Theorem 6.2 (ratio $1 - 1/e$ with the small bids assumption, against the fractional dual optimum), pp. 325-326. <https://static.googleusercontent.com/media/research.google.com/en/us/pubs/archive/41870.pdf>
