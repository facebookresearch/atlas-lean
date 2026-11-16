/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Physlib.SpaceAndTime.Space.Module
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Integrals of coordinate products over `Space d`

## i. Overview

The integral over `Space d` of a product of single-coordinate functions splits as a
product of one-dimensional integrals. This is the reusable step requested by the
`eigenstates_orthonormal` sorry in
`Physlib.QuantumMechanics.HarmonicOscillator.Eigenstates`.

## ii. Key results

* `Space.integral_prod_coord`: `∫ x : Space d, ∏ i, f i (x i) = ∏ i, ∫ t, f i t`.
-/

@[expose] public section

namespace Space

open MeasureTheory

variable {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]

/-- The integral over `Space d` of a product of coordinate functions is the product of
the one-dimensional integrals. Transport along the orthonormal-basis coordinates
(`Space.basis`) and `MeasurableEquiv.toLp`, then Mathlib's finite-product Fubini. -/
theorem integral_prod_coord (f : (i : Fin d) → ℝ → 𝕜) :
    ∫ x : Space d, ∏ i, f i (x i) ∂volume = ∏ i, ∫ t : ℝ, f i t ∂volume := by
  let e : Space d ≃ᵐ (Fin d → ℝ) :=
    basis.measurableEquiv.trans (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm
  have h2 : MeasurePreserving
      ((MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm :
        EuclideanSpace ℝ (Fin d) → (Fin d → ℝ)) volume volume :=
    EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin d)
  have hmp : MeasurePreserving e volume volume :=
    (OrthonormalBasis.measurePreserving_measurableEquiv basis).trans h2
  have hfun : (fun x : Space d => ∏ i, f i (x i))
      = (fun x => (fun g : Fin d → ℝ => ∏ i, f i (g i)) (e x)) := by
    funext x
    apply Finset.prod_congr rfl
    intro i _
    congr 1
  rw [hfun, MeasurePreserving.integral_comp' hmp (fun g : Fin d → ℝ => ∏ i, f i (g i))]
  exact integral_fintype_prod_volume_eq_prod _

end Space
