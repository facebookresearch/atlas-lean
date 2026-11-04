/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Percolation.Universality.RSWBxpAssembly

/-!
# Gluing two square crossings into a rectangle crossing

For a positively associated measure, if both `n × n` halves of `[0, 2n] × [0, n]` are crossed
with probability at least `1/2` and the degenerate column `[n, n] × [0, n]` vertically with
probability at least `v₀`, then `[0, 2n] × [0, n]` is crossed with probability at least `v₀ / 4`.

The self-duality family that derived square bounds at `p = 1/2` from a separation hypothesis
`hsep` (`rst_selfDual_box_crossing_half`, `rst_square_vertical_crossing_half`,
`rst_selfDual_rectangle_crossing_pos`, and the `rba_` square bound they used) was removed: `hsep`
is not planar duality and is false for `[0, 2]²` (`bcc_dichotomy_false`), so those lemmas had no
nondegenerate instance.

## Main results

* `StatMech.Universality.rst_rectangle_crossing_pos`.
-/

@[expose] public section

open Set MeasureTheory SimpleGraph
open scoped ENNReal NNReal

namespace StatMech

namespace Universality

open StatMech.Lattice
open StatMech.RSW.Box
open StatMech.RSW.Strip

/-- For positively associated `μ`: if both `n × n` halves of `[0, 2n] × [0, n]` are crossed with
probability at least `1/2` and the degenerate column `[n, n] × [0, n]` vertically with probability
at least `v₀`, then `[0, 2n] × [0, n]` is crossed with probability at least `v₀ / 4`. -/
theorem rst_rectangle_crossing_pos
    (μ : MeasureTheory.Measure (ConfigSpace (Sym2 (Site 2))))
    [MeasureTheory.IsProbabilityMeasure μ]
    (hpa : PositivelyAssociated μ) {n : ℤ} {v0 : ℝ} (hn : 0 < n)
    (hL : (1 : ℝ) / 2 ≤ μ.real (horizontalCrossingEvent 0 n 0 n))
    (hR : (1 : ℝ) / 2 ≤ μ.real (horizontalCrossingEvent n (2 * n) 0 n))
    (hVlb : v0 ≤ μ.real (verticalCrossingEvent n n 0 n)) (hv0 : 0 ≤ v0) :
    v0 / 4 ≤ μ.real (horizontalCrossingEvent 0 (2 * n) 0 n) :=
  rba_glued_rectangle_lower_bound μ hpa
    (a := 0) (m := n) (m' := n) (b := 2 * n) (c := 0) (d := n)
    (le_of_lt hn) (le_refl n) (by linarith) hn (by linarith) (le_of_lt hn)
    hL hR hVlb hv0

end Universality

end StatMech
