# Crémer–McLean full surplus extraction with correlated types

A seller offers one indivisible object to finitely many bidders. Bidder $i$ has a finite type set $M_i$ and a private value $w_i(s_i) \ge 0$ for the object, the type profile has a common prior whose marginals are strictly positive, and utilities are quasilinear. If for every bidder $i$ the conditional beliefs $\Pr[s_{-i} \mid s_i]$, viewed as vectors indexed by $s_{-i}$, are linearly independent across $s_i$, then for every choice of the value functions $w_i$ there is a dominant-strategy incentive-compatible auction that allocates the object to a bidder with the highest value whenever that value is positive, satisfies interim individual rationality with equality for every type, and so extracts the full expected surplus $\mathbb{E}[\max_i w_i(s_i)]$; conversely, if the condition fails for some bidder, some choice of values admits no such dominant-strategy auction. Full extraction by a Bayesian incentive-compatible auction, with truthful reporting a Bayes–Nash equilibrium, is possible for every choice of values if and only if no type's belief vector is a convex combination of the belief vectors of the bidder's other types.

## Proof sketch

Linear independence of beliefs (full rank of the belief matrix) gives, for any desired interim rents, lotteries $g_i(s_{-i})$ whose expectation under the belief of type $s_i$ equals the expected surplus of type $s_i$ in a Vickrey auction; charging them on top of the Vickrey payments keeps dominant-strategy incentives, since $g_i$ does not depend on bidder $i$'s report, and makes every interim individual rationality constraint bind. Under the weaker convex-independence condition a Farkas-type alternative gives lotteries chosen to have expectation zero under the true type's belief and negative expectation under other types' beliefs, which gives Bayesian incentives.

## Depends on

- [Bayesian incentive compatibility](../revelation-principle/is-bayes-incentive-compatible.md)
- [Interim expected utility](../revelation-principle/interim-utility.md)
- [Bayesian Nash equilibrium](../revelation-principle/is-bayes-nash.md)

## Proof depends on

- [Vickrey–Clarke–Groves theorem](../vickrey-clarke-groves-mechanisms/is-incentive-compatible-groves.md)

## Sources

- Jacques Cremer and Richard P. McLean, "Full Extraction of the Surplus in Bayesian and Dominant Strategy Auctions", Econometrica 56(6), 1988, pp. 1247–1257, Lemma 1 (full extraction means binding individual rationality and efficient allocation), Theorem 1 (dominant-strategy auctions; the full-rank condition on the belief matrices) and Theorem 2 (Bayesian auctions; no type's belief is a convex combination of the other types' beliefs).
