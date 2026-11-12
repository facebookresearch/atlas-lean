/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Consumer.TwoGood
public import MathlibExt.Economics.SecondWelfareTheorem
import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Local nonsatiation implies budget exhaustion (Atlas EC02.T02)

Source: J. Levin, *Consumer Theory*, Stanford Econ 202 lecture notes (2004), §2,
Proposition 4 ("Walras' Law" for one consumer): if preferences are locally non-satiated, then for
any `(p, w)` and `x ∈ x(p, w)`, `p · x = w`. Local nonsatiation (Levin–Milgrom, *Introduction to
Choice Theory*, Definition 8) on the consumption set `ℝ^L_+` is Atlas's
`SecondWelfareTheorem.LocallyNonsatiated`. No sign condition on prices is needed.
-/

namespace MathlibExt.Economics.Consumer

open Matrix

open SecondWelfareTheorem (consumptionSet)

/-- Levin, Proposition 4: with a locally nonsatiated utility, every Marshallian demand on `ℝ^L_+`
exhausts the budget. -/
theorem dotProduct_eq_of_isMarshallianDemand {L : Type*} [Fintype L] {u : (L → ℝ) → ℝ}
    {p : L → ℝ} {w : ℝ} {x : L → ℝ} (hu : SecondWelfareTheorem.LocallyNonsatiated u)
    (hx : IsMarshallianDemand u (consumptionSet L) p w x) : p ⬝ᵥ x = w := by
  obtain ⟨⟨hxmem, hxle⟩, hxopt⟩ := hx
  by_contra hne
  have hlt : p ⬝ᵥ x < w := lt_of_le_of_ne hxle hne
  have hcont : Continuous (fun z : L → ℝ => p ⬝ᵥ z) := by
    unfold dotProduct
    continuity
  obtain ⟨δ, hδpos, hδ⟩ := (Metric.continuous_iff.mp hcont x (w - p ⬝ᵥ x) (sub_pos.mpr hlt))
  obtain ⟨z, hzmem, hdist, hgt⟩ := hu x hxmem δ hδpos
  have hdist2 := hδ z hdist
  rw [Real.dist_eq] at hdist2
  have hzaff : p ⬝ᵥ z ≤ w := by
    have h1 : p ⬝ᵥ z - p ⬝ᵥ x ≤ |p ⬝ᵥ z - p ⬝ᵥ x| := le_abs_self _
    linarith
  have hzbs : z ∈ budgetSet (consumptionSet L) p w := ⟨hzmem, hzaff⟩
  have hle := hxopt z hzbs
  linarith

end MathlibExt.Economics.Consumer
