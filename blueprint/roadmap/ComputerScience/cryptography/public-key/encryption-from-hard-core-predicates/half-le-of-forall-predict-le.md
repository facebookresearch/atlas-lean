# An unbounded predictor always wins

For every key distribution, permutation family and predicate, if every predictor wins the
[prediction experiment](predict-game.md) with probability at most $\tfrac12 + \varepsilon$, then
$\varepsilon \ge \tfrac12$: the predictor $y \mapsto b_\alpha(p_\alpha^{-1}(y))$, which inverts the
permutation, always wins. In this concrete model, where every function counts as a predictor, the
theorems that assume the all-predictor hypothesis are therefore vacuous.
