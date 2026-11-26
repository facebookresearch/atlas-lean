# Position assignments are optimal iff supported by locally envy-free prices

An assignment in a position auction (with at least $k$ bidders) is optimal if and only if there exist prices under which it is locally envy-free. The minimal nonnegative locally envy-free prices are given by $p_{k-1}$ equal to the highest unassigned value (or $0$ if all bidders are assigned) and, for $s < k - 1$, $\mu_s p_s = (\mu_s - \mu_{s+1})\, v_{\sigma(s+1)} + \mu_{s+1} p_{s+1}$.

## Proof sketch

Adding the two local envy-freeness inequalities between adjacent slots gives $(\mu_s - \mu_{s+1})(v_{\sigma(s)} - v_{\sigma(s+1)}) \ge 0$, so values are sorted; conversely for a sorted assignment the recursion defines prices satisfying all local constraints.

## Depends on

- [Position auction and locally envy-free assignment](position-auction-and-locally-envy-free-assignment.md)

## Sources

- Sebastien Lahaie, David M. Pennock, Amin Saberi and Rakesh V. Vohra, "Sponsored Search Auctions", Algorithmic Game Theory, Cambridge University Press, 2007.
