# Stereographic snapping to rational points of the 3-sphere

Let `z` be a unit vector in `ℝ⁴` and let `w ∈ ℚ⁴` approximate it
coordinatewise, `|w j - z j| ≤ δ` for every `j`, with `δ ≤ 1/8`. If `k` is a
coordinate of largest magnitude of `w` (`|w j| ≤ |w k|` for all `j`), then
the rational point `stereoSnap w k` of the unit sphere `S^3` lies within
Euclidean distance `4 * δ` of `z`.

Here `stereoSnap w k` is the rational point obtained by projecting `w`
stereographically from the pole `-(sign w_k) e_k` (with sign `+1` when `w k
≥ 0`) and inverting the projection exactly over `ℚ`, which gives a rational
point of the unit sphere.
