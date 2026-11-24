# A game with given Lotka–Volterra parameters

For a finite set `ι`, growth rates `r : ι → ℝ` and an interaction matrix `B` on `ι`, the game on the
strategies `ι ∪ {o}`, with `o` an extra reference strategy, has payoff `B_ij` for `i` against `j`,
payoff `r_i` for `i` against `o`, and payoff `0` for `o` against every strategy. Its
[growth rates](lv-growth.md) are `r` and its [interaction matrix](lv-interaction.md) is `B`, so
every pair `(r, B)` arises from a game.
