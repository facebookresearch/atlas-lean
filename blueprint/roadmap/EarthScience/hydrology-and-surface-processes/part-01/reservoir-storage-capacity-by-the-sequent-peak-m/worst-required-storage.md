# Worst required storage over the horizon

For required releases `R` and inflows `Q` over `n` time steps, with deficits `dᵢ = Rᵢ - Qᵢ`, the
worst required storage `W` is the maximal segment score of the deficit list: the largest net
deficit `d_i + … + d_{j-1}` over the windows of consecutive steps `0 ≤ i ≤ j ≤ n`, the empty window
counting as `0`. It is the largest [storage deficit](required-storage-at.md) `K_t`, attained at
some `t ≤ n` ([proof](required-storage-at-le-worst-and-exists.md)), and the least capacity of a
reservoir that starts full and meets every release over the horizon
([feasibility](storage-feasible-iff.md)).
