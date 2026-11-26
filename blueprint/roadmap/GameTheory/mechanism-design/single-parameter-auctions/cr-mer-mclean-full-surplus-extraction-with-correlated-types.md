# Crémer–McLean full surplus extraction with correlated types

Let finitely many agents have finite type spaces, a common prior with strictly positive marginals, and quasilinear valuations over outcomes. If for every agent $i$ the conditional beliefs $\Pr[t_{-i} \mid t_i]$, viewed as vectors indexed by $t_{-i}$, are linearly independent across $t_i$, then for every efficient outcome rule there are transfers (opponent-contingent side payments) making truthful reporting a Bayes–Nash equilibrium with interim individual rationality binding for every type, so that the designer extracts the full expected surplus. If the outcome rule is implemented by a DSIC mechanism (for example VCG), the extraction can be made dominant-strategy compatible with Bayesian participation.

## Proof sketch

Linear independence of beliefs (Farkas' lemma) gives, for any desired interim rents, lotteries $g_i(t_{-i})$ whose expectation under belief $t_i$ equals minus the rent of type $t_i$ while misreports face strictly worse expected lotteries; adding them to an incentive-compatible efficient mechanism removes all information rents.

## Depends on

- [Bayesian incentive compatibility](../revelation-principle/is-bayes-incentive-compatible.md)
- [Interim expected utility](../revelation-principle/interim-utility.md)
- [Bayesian Nash equilibrium](../revelation-principle/is-bayes-nash.md)

## Proof depends on

- [Vickrey–Clarke–Groves theorem](../vickrey-clarke-groves-mechanisms/is-incentive-compatible-groves.md)

## Sources

- Jacques Cremer and Richard P. McLean, "Full Extraction of the Surplus in Bayesian and Dominant Strategy Auctions", Econometrica, 1988.
