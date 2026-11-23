# With lattice scores, the one-sequence tail forces K = 0

Let `q` and `f` be real weights and scores on a finite alphabet, `θ > 0`, `h > 0` and `K` real, with
every score `f b` in the lattice `hℤ`. If `(q, f)` has the [one-sequence tail](../../../Biology/bioinformatics/sequence-alignment/two-sequence-karlin-altschul-statistics/one-sequence-tail.md)
with constants `θ` and `K`, that is `P(M_L > t) = (K + o(1)) L e^{-θ t}`, uniformly as `L → ∞` and
`L e^{-θ t} → 0` over thresholds `t ≤ η L`, for the
[score probability](score-prob.md) of `{M_L > t}`,
then `K = 0`. Indeed `P(M_L > t)`
[is constant on each open lattice cell](score-prob-lt-max-seg-score-eq-of-lattic.md), while
`K L e^{-θ t}` drops by the factor `e^{-θ h / 2}` across half a cell.
