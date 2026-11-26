# Upper envelope bound for loads in a box

Let `ι` be a finite set of load coordinates, `η` a fixed influence vector and `cap` a vector of
pattern capacities, both indexed by `ι`. Every load `f` with `0 ≤ f_i ≤ cap_i` for all `i` has
response `η · f` at most the upper envelope value `∑_i cap_i * max(η_i, 0)`. Each coordinate
contributes at most its envelope term, whatever the sign of its influence coefficient. No sign
condition on the capacities is stated: the box hypotheses already force `cap_i ≥ 0`.
