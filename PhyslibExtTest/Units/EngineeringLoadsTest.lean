/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Units.EngineeringLoads
import Mathlib.Tactic.NormNum

/-!
# Tests for `PhyslibExt.Units.EngineeringLoads`

* the type interface: a force plus a pressure does not
  elaborate, while a force plus a pressure force does;
* pressure on a positive area: numeric conversion and the
  zero-area control;
* the role limit in the not-claimed paragraph: `WithDim`
  itself adds two absolute temperatures;
* retagging round trips and a couple fixture (zero resultant,
  nonzero moment), stable under unit conversion.
-/

@[expose] public section

namespace PhyslibExtTest.Units.EngineeringLoads

open Dimension _root_.Units.QuantityDimensions
  _root_.Units.EngineeringQuantities _root_.Units.EngineeringLoads
open PhyslibExt.Mechanics.HarmonicMechanics

/-! ## A. The type interface -/

/-- A force plus a pressure is rejected by the type
interface, while a force plus the pressure force on a
positive area elaborates. The rejection is by the dimension
term: even the equal-valued moment and energy dimensions are
not identified without an explicit `WithDim.cast`, and
`⟨p.val⟩` retags any value by hand. -/
example (F : WithDim forceDim ℝ) (p : WithDim stressDim ℝ)
    (A : WithDim (single ISQDimensionBase.length ^ (2 : ℕ)) ℝ)
    (hA : 0 < A.val) : True := by
  fail_if_success have _bad := F + p
  have _ok : WithDim forceDim ℝ := F + pressureForce p A hA
  trivial

/--
error: failed to synthesize instance of type class
  HAdd (WithDim forceDim ℝ) (WithDim stressDim ℝ)
-/
#guard_msgs (error, substring := true) in
example (F : WithDim forceDim ℝ) (p : WithDim stressDim ℝ) :
    WithDim forceDim ℝ := F + p

/-- Distinctness consequence of the nodup certificate: a
pressure is not a moment. -/
example : stressDim ≠ forceDim * single ISQDimensionBase.length := by
  have h := forceDim_stressDim_moment_lineLoad_nodup
  intro heq
  rw [heq] at h
  simp at h

/-! ## B. Pressure on a positive area -/

/-- Pressure `3` on area `2` gives outward-normal
force `-6` (tension-positive convention). -/
example : (pressureForce (⟨3⟩ : WithDim stressDim ℝ)
    (⟨2⟩ : WithDim (single ISQDimensionBase.length ^ (2 : ℕ)) ℝ)
    (by norm_num)).val = -6 := by
  rw [pressureForce_val]
  norm_num

/-- Its tension-positive normal stress is `-3`. -/
example : normalStress (pressureForce (⟨3⟩ : WithDim stressDim ℝ)
      (⟨2⟩ : WithDim (single ISQDimensionBase.length ^ (2 : ℕ)) ℝ)
      (by norm_num))
    (⟨2⟩ : WithDim (single ISQDimensionBase.length ^ (2 : ℕ)) ℝ)
    (by norm_num) = -⟨3⟩ :=
  normalStress_pressureForce _ _

/-- Zero-area control: the round trip needs positive area. -/
example : (3 : ℝ) * 0 / 0 ≠ 3 := by norm_num

/-! ## C. Role limits -/

/-- Control for the not-claimed paragraph: `WithDim`
itself adds two absolute temperatures; physical roles
at one dimension are not kept apart by the type. -/
example (T1 T2 : WithDim temperatureDim ℝ) :
    WithDim temperatureDim ℝ := T1 + T2

/-! ## D. Retagging and the couple fixture -/

example {ι : Type} (F : WithDim forceDim (ι → ℝ)) :
    (⟨F.val⟩ : WithDim forceDim (ι → ℝ)) = F := rfl

example {ι : Type} (f : ι → ℝ) :
    (⟨f⟩ : WithDim forceDim (ι → ℝ)).val = f := rfl

example (M : WithDim (forceDim * single ISQDimensionBase.length) ℝ) :
    (⟨M.val⟩ :
      WithDim (forceDim * single ISQDimensionBase.length) ℝ) = M := rfl

/-- Lever arms of the couple: `(1, 0)` and `(0, 0)`. -/
private abbrev xC :
    Fin 2 → WithDim (single ISQDimensionBase.length) (Fin 2 → ℝ) :=
  ![⟨![1, 0]⟩, ⟨![0, 0]⟩]

/-- The couple forces `(0, 1)` and `(0, -1)`. -/
private abbrev FC : Fin 2 → WithDim forceDim (Fin 2 → ℝ) :=
  ![⟨![0, 1]⟩, ⟨![0, -1]⟩]

/-- The couple has zero resultant. -/
example : ∑ i, FC i = 0 := by
  apply WithDim.ext
  rw [sum_force_val]
  simp [resultantForce, Fin.sum_univ_two]

/-- The couple has nonzero moment `1`. -/
example : forceMoment2D xC FC ≠ 0 := by
  intro h
  have hv := congrArg WithDim.val h
  rw [forceMoment2D_val] at hv
  norm_num [moment2D, Fin.sum_univ_two] at hv

/-- Metre-to-millimetre moment factor `1000 * 1000`. -/
private lemma dimScale_si_mm_moment :
    (siScale.dimScale mmScale
      (forceDim * single ISQDimensionBase.length) : ℝ)
      = 1000000 := by
  have hl : (siScale.dimScale mmScale
      (single ISQDimensionBase.length) : ℝ) = 1000 := by
    rw [Units.QuantityDimensions.dimScale_single, NNReal.coe_div]
    norm_num [siScale, mmScale]
  rw [Units.QuantityDimensions.dimScale_mul, dimScale_si_mm_forceDim, hl]
  norm_num

/-- The couple's moment in millimetre units is the moment
factor times the original moment value `1`. -/
example : (forceMoment2D
      (fun i => (⟨(siScale.dimScale mmScale
          (single ISQDimensionBase.length) : ℝ) • (xC i).val⟩ :
        WithDim (single ISQDimensionBase.length) (Fin 2 → ℝ)))
      (fun i => (⟨(siScale.dimScale mmScale forceDim : ℝ) • (FC i).val⟩ :
        WithDim forceDim (Fin 2 → ℝ)))).val = 1000000 := by
  have h := congrArg WithDim.val
    (forceMoment2D_dimScale siScale mmScale xC FC)
  rw [dimScale_si_mm_moment] at h
  rw [h, forceMoment2D_val]
  norm_num [moment2D, Fin.sum_univ_two]

/-- The couple does not balance, before or after unit
conversion. -/
example : ¬ (∑ i, (⟨(siScale.dimScale mmScale forceDim : ℝ)
        • (FC i).val⟩ : WithDim forceDim (Fin 2 → ℝ)) = 0 ∧
      forceMoment2D
          (fun i => (⟨(siScale.dimScale mmScale
              (single ISQDimensionBase.length) : ℝ) • (xC i).val⟩ :
            WithDim (single ISQDimensionBase.length) (Fin 2 → ℝ)))
          (fun i => (⟨(siScale.dimScale mmScale forceDim : ℝ)
              • (FC i).val⟩ :
            WithDim forceDim (Fin 2 → ℝ))) = 0) := by
  rw [planarLoad_balance_dimScale_iff]
  intro h
  have hne : forceMoment2D xC FC ≠ 0 := by
    intro hm
    have hv := congrArg WithDim.val hm
    rw [forceMoment2D_val] at hv
    norm_num [moment2D, Fin.sum_univ_two] at hv
  exact hne h.2

#print axioms Units.EngineeringLoads.forceDim_ne_stressDim
#print axioms Units.EngineeringLoads.forceDim_stressDim_moment_lineLoad_nodup
#print axioms Units.EngineeringLoads.sum_force_val
#print axioms Units.EngineeringLoads.sum_force_eq_zero_iff
#print axioms Units.EngineeringLoads.sum_retag_force
#print axioms Units.EngineeringLoads.forceMoment2D_val
#print axioms Units.EngineeringLoads.forceMoment2D_retag
#print axioms Units.EngineeringLoads.forceMoment2D_eq_zero_iff
#print axioms Units.EngineeringLoads.planarLoad_balance_iff
#print axioms Units.EngineeringLoads.force_components_dimScale_round_trip
#print axioms Units.EngineeringLoads.force_vector_withDim_dimScale_round_trip
#print axioms Units.EngineeringLoads.moment_dimScale_round_trip
#print axioms Units.EngineeringLoads.moment_withDim_dimScale_round_trip
#print axioms Units.EngineeringLoads.forceMoment2D_dimScale
#print axioms Units.EngineeringLoads.planarLoad_balance_dimScale_iff
#print axioms Units.EngineeringLoads.pressureForce_val
#print axioms Units.EngineeringLoads.normalStress_pressureForce
#print axioms Units.EngineeringLoads.pressureForce_normalStress
end PhyslibExtTest.Units.EngineeringLoads
