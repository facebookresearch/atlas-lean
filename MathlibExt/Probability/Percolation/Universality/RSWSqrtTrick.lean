/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Percolation.Universality.RSWBxpAssembly

/-!
# Self-duality lower bounds for box crossings at `p = 1/2`

Under `ℙ_{1/2}`, if the complement of the open left–right crossing of a box is contained in the
`dualConfig` bottom–top crossing (`hsep`) and the box has equiprobable crossings (`hsqsym`), the
left–right crossing has probability at least `1/2`; gluing two such boxes with a vertical crossing
of the overlap gives a lower bound for a `2n × n` rectangle.

The separation hypothesis `hsep` is not planar duality and is false for `[0, 2]²`
(`bcc_dichotomy_false`), so these lemmas have no known nondegenerate instance; see
`rst_selfDual_box_crossing_half`.

## Main results

* `StatMech.Universality.rst_selfDual_box_crossing_half`.
* `StatMech.Universality.rst_rectangle_crossing_pos`,
  `StatMech.Universality.rst_selfDual_rectangle_crossing_pos`.
-/

@[expose] public section

open Set MeasureTheory SimpleGraph
open scoped ENNReal NNReal

namespace StatMech

namespace Universality

open StatMech.Lattice
open StatMech.RSW.Box
open StatMech.RSW.Strip

/-- `ℙ_{1/2}(H[a, b] × [c, d]) ≥ 1/2`, given `hsep` and the symmetry `ℙ_{1/2}(V) = ℙ_{1/2}(H)`.

See also `StatMech.RSW.Box.square_crossing_ge_half`, the same argument for a general measure.

The hypothesis `hsep` ("no open left–right crossing implies a `dualConfig` bottom–top crossing")
is not planar duality: `dualConfig` is the rotated complement on the primal lattice, so
`dualVerticalCrossingEvent a b c d` is a closed left–right crossing of the rotated rectangle
`[c, d] × [-b, -a]`. `bcc_dichotomy_false` shows `hsep` fails for `[0, 2]²`; it is not known to
hold for any nondegenerate rectangle. -/
theorem rst_selfDual_box_crossing_half (a b c d : ℤ)
    (hmeasH : MeasurableSet (horizontalCrossingEvent a b c d))
    (hmeasV : MeasurableSet (verticalCrossingEvent a b c d))
    (hsep : (horizontalCrossingEvent a b c d)ᶜ ⊆ dualVerticalCrossingEvent a b c d)
    (hsqsym : halfMeasure.real (verticalCrossingEvent a b c d)
                = halfMeasure.real (horizontalCrossingEvent a b c d)) :
    (1 : ℝ) / 2 ≤ halfMeasure.real (horizontalCrossingEvent a b c d) := by
  have hselfDual : halfMeasure.real (dualVerticalCrossingEvent a b c d)
      = halfMeasure.real (horizontalCrossingEvent a b c d) := by
    rw [rba_dualVerticalCrossing_eq a b c d hmeasV, hsqsym]
  have hcompl : halfMeasure.real (horizontalCrossingEvent a b c d)ᶜ
      = 1 - halfMeasure.real (horizontalCrossingEvent a b c d) := by
    rw [measureReal_compl hmeasH, probReal_univ]
  have hmono : halfMeasure.real (horizontalCrossingEvent a b c d)ᶜ
      ≤ halfMeasure.real (dualVerticalCrossingEvent a b c d) :=
    measureReal_mono hsep
  rw [hselfDual, hcompl] at hmono
  linarith

/-- Vertical form of `rba_self_dual_square_half`: `ℙ_{1/2}(V[0, n]²) ≥ 1/2` under the same
hypotheses, including the separation hypothesis `hsep`, which fails for `[0, 2]²`. -/
theorem rst_square_vertical_crossing_half (n : ℤ)
    (hmeasH : MeasurableSet (horizontalCrossingEvent 0 n 0 n))
    (hmeasV : MeasurableSet (verticalCrossingEvent 0 n 0 n))
    (hsep : (horizontalCrossingEvent 0 n 0 n)ᶜ ⊆ dualVerticalCrossingEvent 0 n 0 n)
    (hsqsym : halfMeasure.real (verticalCrossingEvent 0 n 0 n)
                = halfMeasure.real (horizontalCrossingEvent 0 n 0 n)) :
    (1 : ℝ) / 2 ≤ halfMeasure.real (verticalCrossingEvent 0 n 0 n) := by
  rw [hsqsym]
  exact rba_self_dual_square_half n hmeasH hmeasV hsep hsqsym

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

/-- `rst_rectangle_crossing_pos` for `ℙ_{1/2}`, with the two square bounds obtained from
`rst_selfDual_box_crossing_half`; it inherits that lemma's separation hypotheses `hsepL`, `hsepR`,
which fail for `[0, 2]²`. -/
theorem rst_selfDual_rectangle_crossing_pos
    (hpa : PositivelyAssociated halfMeasure) {n : ℤ} {v0 : ℝ} (hn : 0 < n)
    (hmeasHL : MeasurableSet (horizontalCrossingEvent 0 n 0 n))
    (hmeasVL : MeasurableSet (verticalCrossingEvent 0 n 0 n))
    (hsepL : (horizontalCrossingEvent 0 n 0 n)ᶜ ⊆ dualVerticalCrossingEvent 0 n 0 n)
    (hsqsymL : halfMeasure.real (verticalCrossingEvent 0 n 0 n)
                = halfMeasure.real (horizontalCrossingEvent 0 n 0 n))
    (hmeasHR : MeasurableSet (horizontalCrossingEvent n (2 * n) 0 n))
    (hmeasVR : MeasurableSet (verticalCrossingEvent n (2 * n) 0 n))
    (hsepR : (horizontalCrossingEvent n (2 * n) 0 n)ᶜ
                ⊆ dualVerticalCrossingEvent n (2 * n) 0 n)
    (hsqsymR : halfMeasure.real (verticalCrossingEvent n (2 * n) 0 n)
                = halfMeasure.real (horizontalCrossingEvent n (2 * n) 0 n))
    (hVlb : v0 ≤ halfMeasure.real (verticalCrossingEvent n n 0 n)) (hv0 : 0 ≤ v0) :
    v0 / 4 ≤ halfMeasure.real (horizontalCrossingEvent 0 (2 * n) 0 n) := by
  have hL : (1 : ℝ) / 2 ≤ halfMeasure.real (horizontalCrossingEvent 0 n 0 n) :=
    rba_self_dual_square_half n hmeasHL hmeasVL hsepL hsqsymL
  have hR : (1 : ℝ) / 2 ≤ halfMeasure.real (horizontalCrossingEvent n (2 * n) 0 n) :=
    rst_selfDual_box_crossing_half n (2 * n) 0 n hmeasHR hmeasVR hsepR hsqsymR
  exact rst_rectangle_crossing_pos halfMeasure hpa hn hL hR hVlb hv0

end Universality

end StatMech
