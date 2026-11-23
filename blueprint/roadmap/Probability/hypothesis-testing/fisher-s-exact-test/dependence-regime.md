# Dependence regimes for the per-variant p-values

A dependence regime is one of three hypotheses on the joint law of `m` per-variant p-values, under
which a downstream Benjamini–Hochberg-type step is known to control the false discovery rate on
valid p-values: the p-values are mutually independent (Benjamini–Hochberg at level `q`); they are
positively regression dependent on the subset of true nulls, PRDS (Benjamini–Hochberg at level
`q`); or nothing is assumed, and the step needs a procedure valid under arbitrary dependence, for
example Benjamini–Yekutieli, which is Benjamini–Hochberg at level `q / H_m` with
`H_m = 1 + 1/2 + ⋯ + 1/m`. What each regime asserts is its [hypothesis](holds.md). Choosing a regime
is an assumption about the joint law of the p-values; it does not follow from the per-variant null.
