# Probability bound on the false discovery proportion of the BH-selected set

Under the
hypotheses of `integral_fdp_bhRejections_tailPValue_le` (tail-calibrated tests with PRDS
p-values), for `q ∈ (0, 1]` and `δ > 0`, the event that the gene set selected by BH at level `q`
has false discovery proportion below the fixed number `q / δ` has probability at least `1 - δ`.
The statement is informative only for `q ≤ δ < 1`: for `δ < q` the level exceeds `1`, which the
FDP never does, and for `δ ≥ 1` the bound `1 - δ` is not positive.
`measure_le_fdp_bhRejections_tailPValue_le` gives the sharper level `q |H0| / (m δ)` when
`H0.Nonempty` (which implies `m > 0` and the cutoff is positive, as that lemma requires `c > 0`).
When `H0 = ∅`, FDP is identically `0` and the strict event `{FDP < 0}` is empty, so no sharper
strict bound at cutoff `0` is claimed.
