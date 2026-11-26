# Position auction and locally envy-free assignment

In a *position auction* there are $k$ slots with click-through rates $\mu_0 > \mu_1 > \dots > \mu_{k-1} > 0$ and bidders with per-click values $v_i$. An assignment fills the slots with distinct bidders. Prices $p_0, \dots, p_{k-1}$ per click make an assignment *locally envy-free* if no bidder prefers the slot directly above its own at that slot's price, no bidder prefers its own slot below, and (treating unassigned bidders as occupying a dummy slot of rate $0$ and price $0$) no unassigned bidder envies the last slot. An assignment is *optimal* if it maximizes $\sum_s \mu_s v_{\sigma(s)}$, equivalently is assortative (values nonincreasing along slots, unassigned values below all assigned ones).

## Depends on

- [Single-parameter quasilinear mechanisms: model, DSIC and IR](../myerson-s-lemma-and-revenue-equivalence/remaining-clauses-of-single-parameter-quasilinear-mechanisms.md)
- [Social welfare](../vickrey-clarke-groves-mechanisms/welfare.md)

## Sources

- Sebastien Lahaie, David M. Pennock, Amin Saberi and Rakesh V. Vohra, "Sponsored Search Auctions", Algorithmic Game Theory, Cambridge University Press, 2007.
