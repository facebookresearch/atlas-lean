# Aldous's tightness criterion in `D((0,1))`

**Aldous's tightness criterion in `D([0,1])`** (for the step processes of triangular
arrays).

Let row `n` of the array `ξ` be adapted to the filtration `𝓕 n` (`ξ n i` is
`𝓕 n (i + 1)`-measurable). If the largest increment of row `n` tends to `0` in probability and
the partial sums satisfy Aldous's condition (`AldousCondition`, the two-stopping-time form of
Jacod–Shiryaev VI.4.5 (ii)), then the laws of the step processes
`arrayStepProcess n ξ : Ω → D([0,1])`, `t ↦ ∑_{i < ⌊n t⌋} ξ n i`, are tight for the Skorokhod
J1 topology.

## Sources

- Jacod–Shiryaev (2003), Theorem VI.4.5 (Aldous's criterion for tightness in `D`), for step processes with asymptotically negligible jumps (Proposition VI.3.26); Aldous (1978). With `hjump` the criterion reduces to `C`-tightness, where paths starting at `0` make the compact-containment condition (i) of VI.4.5 unnecessary. (Without `hjump` condition (i) is needed: `n · 1{t ≥ U}` with `U` uniform starts at `0` and satisfies Aldous's condition, but its suprema are not tight.) Proof: `C`-tightness of the polygons (`isTightMeasureSet_arrayPolygon_of_aldousCondition`), transferred to `D` by `isTightMeasureSet_arrayStepProcess_of_isTightMeasureSet_arrayPolygon`.
