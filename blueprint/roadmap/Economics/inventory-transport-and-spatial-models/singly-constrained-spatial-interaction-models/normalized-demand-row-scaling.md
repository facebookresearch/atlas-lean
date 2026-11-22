# Positive rescaling of weights leaves the flows unchanged

Positive rescaling of a demand weight row leaves the normalized demand unchanged: for `c > 0` and
weights with positive sum over the finite destination set `s` (`∑_{j ∈ s} wⱼ > 0`), distributing the
origin total `O` by the weights `c wⱼ` gives the same flow to every destination `i` as distributing
by `wⱼ`: `O (c wᵢ) / ∑_{j ∈ s} c wⱼ = O wᵢ / ∑_{j ∈ s} wⱼ`. The scale cancels in the normalization;
reachability (which destinations are in `s`) is unchanged.
