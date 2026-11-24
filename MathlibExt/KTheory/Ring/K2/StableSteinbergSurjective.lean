/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.KTheory.Ring.K2.StableSteinbergToElementary
public import Mathlib.Algebra.Group.Subgroup.Ker

/-! # Surjectivity onto the stable elementary group

Proves that the canonical map from the stable Steinberg group onto `StableE` is surjective.
-/

namespace AlgebraicKTheory

namespace StableSteinberg

/-- The canonical map `St(R) →* E∞(R)` is surjective. -/
public theorem toStableE_surjective {R : Type*} [Ring R] :
    Function.Surjective (toStableE (R := R)) := by
  rw [← MonoidHom.range_eq_top]
  have h_top :
      Subgroup.closure
          ((stableElementarySubgroup (R := R)).subtype ⁻¹'
            stableElementarySet (R := R)) = ⊤ :=
    Subgroup.closure_preimage_eq_top (stableElementarySet (R := R))
  have h_le :
      Subgroup.closure
          ((stableElementarySubgroup (R := R)).subtype ⁻¹'
            stableElementarySet (R := R)) ≤
        MonoidHom.range (toStableE (R := R)) := by
    rw [Subgroup.closure_le]
    intro y hy
    have h_mem : (y : StableGL R) ∈ stableElementarySet R := hy
    obtain ⟨n, i, j, hij, a, h_eq⟩ := h_mem
    have hij_val : i.val ≠ j.val := fun h => hij (Fin.eq_of_val_eq h)
    refine MonoidHom.mem_range.mpr ⟨x i.val j.val hij_val a, ?_⟩
    have h_to : toStableE (R := R) (x i.val j.val hij_val a) =
        StableE.natElementary (R := R) i.val j.val hij_val a :=
      toStableE_x i.val j.val hij_val a
    have h_nat : StableE.natElementary (R := R) i.val j.val hij_val a =
        StableE.elementary n i j hij a :=
      StableE.natElementary_fin n i j hij a
    have h_gen : toStableE (R := R) (x i.val j.val hij_val a) =
        StableE.elementary (R := R) n i j hij a := by
      rw [h_to, h_nat]
    have h_y : y = StableE.elementary (R := R) n i j hij a := by
      apply Subtype.ext
      have h_coe : (StableE.elementary (R := R) n i j hij a : StableGL R) =
          StableGL.of (Matrix.GeneralLinearGroup.elementary i j hij a) :=
        StableE.coe_elementary i j hij a
      rw [h_coe]
      exact h_eq
    rw [h_gen, h_y]
  have h_top_le : (⊤ : Subgroup (StableE R)) ≤ MonoidHom.range (toStableE (R := R)) :=
    h_top ▸ h_le
  exact le_antisymm le_top h_top_le

end StableSteinberg

end AlgebraicKTheory
