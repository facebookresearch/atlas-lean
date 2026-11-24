# Single-epoch conditional failure probability

For nonnegative scenario weights `p`, an
increasing system event `S`, nonnegative rates, a sensor with gain `g ≠ 0` on component `i₀`, its
bin event `A` at time `t` with `P(A) > 0`, and the system failure event `F` at `t`: the weights
normalized on `A` are a finite distribution, they give `F` the probability `P(A ∩ F) / P(A)`, which
lies in `[0, 1]`, and `A ∩ F` is the set of scenarios whose reading is in the bin and whose
configuration of components still below threshold at `t` is not in `S`.
