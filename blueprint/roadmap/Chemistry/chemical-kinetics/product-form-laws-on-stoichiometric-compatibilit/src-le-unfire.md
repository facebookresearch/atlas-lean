# The source complex fits into the predecessor of every state

Let `N` be a [chemical reaction network](../../../Dynamics/smooth-dynamics/reaction-network.md) with
species set `S` and reaction set `ρ`. For every reaction `r` and every state `x ∈ ℕ^S`, the
[state before one firing](../../../Biology/systems-biology/stochastic-mass-action-metabolic-control-and-flu/unfire.md)
of `r`, `x - prod(r) + src(r)`, contains the source complex: `src(r) ≤ x - prod(r) + src(r)`
coordinatewise. The difference `x_s - prod(r)_s` is natural-number subtraction, truncated at `0`, so
the inequality holds for every `x`, also when `prod(r) ≤ x` fails.
