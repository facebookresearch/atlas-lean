# A plant built from network data has the network supply and loss

For all network data with a [branch partition](../energy-balance-of-rlc-networks/is-branch-partition.md), all signals `φ`, `j`, `v`
and `i`, and every time `t`, the [plant built from the data](plant-of-network.md) along the
[trajectory built from the signals](trajectory-of-signals.md) has
[supply rate](plant-supply-rate.md) `φ(t) · j(t) - ∑_{e ∈ S} v_e(t) i_e(t)` and
[loss rate](plant-loss-rate.md) `∑_{e ∈ R} R_e i_e(t)²`.
