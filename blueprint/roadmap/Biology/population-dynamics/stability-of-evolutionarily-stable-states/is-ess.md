# Evolutionarily stable state of a matrix game

For a finite set `ι` of strategies and a payoff matrix `A` on `ι`, a vector `p : ι → ℝ` is an
evolutionarily stable state (Maynard Smith and Price 1973; Hofbauer and Sigmund 1998, (6.3)–(6.4))
when `p` is a mixed strategy (`p_i ≥ 0` for every `i` and `∑_i p_i = 1`) and every mixed strategy
`q ≠ p` satisfies either `q · A p < p · A p`, or `q · A p = p · A p` and `q · A q < p · A q`.
