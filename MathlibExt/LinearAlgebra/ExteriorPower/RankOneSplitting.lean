/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import MathlibExt.LinearAlgebra.ExteriorPower.ContractionWedge

/-!
# Rank-one splittings of exterior powers

The exterior-algebra map induced by the identity minus a rank-one operator
is the identity minus exterior multiplication followed by contraction.
Applied to the last summand of a product, this formula gives a degreewise
splitting of its exterior powers.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace ExteriorAlgebra

universe u v

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

/-- The literal complement of a rank-one linear operator. -/
def rankOneComplement (ε : M →ₗ[R] R) (e : M) : M →ₗ[R] M :=
  LinearMap.id - (LinearMap.toSpanSingleton R M e).comp ε

@[simp]
theorem rankOneComplement_apply (ε : M →ₗ[R] R) (e m : M) :
    rankOneComplement R M ε e m = m - ε m • e := rfl

/-- The original exterior-algebra map of a rank-one perturbation of the
identity has this exact contraction formula, with no basis choice. -/
theorem map_rankOneComplement_add_wedge_contract
    (ε : M →ₗ[R] R) (e : M) (z : ExteriorAlgebra R M) :
    map (rankOneComplement R M ε e) z +
      ι R e * CliffordAlgebra.contractLeft ε z = z := by
  induction z using CliffordAlgebra.left_induction with
  | algebraMap r => simp [CliffordAlgebra.contractLeft_algebraMap]
  | add z w hz hw =>
      simpa only [map_add, mul_add, add_add_add_comm] using congrArg₂ (· + ·) hz hw
  | ι_mul z m hz =>
      have hp : map (rankOneComplement R M ε e) z =
          z - ι R e * CliffordAlgebra.contractLeft ε z := eq_sub_of_add_eq hz
      have hezero : ι R e * (ι R e * CliffordAlgebra.contractLeft ε z) = 0 := by
        rw [← mul_assoc, ι_sq_zero, zero_mul]
      have hanti : ι R e * (ι R m * CliffordAlgebra.contractLeft ε z) =
          -(ι R m * (ι R e * CliffordAlgebra.contractLeft ε z)) := by
        rw [← mul_assoc,
          eq_neg_of_add_eq_zero_left (ι_add_mul_swap (R := R) e m), neg_mul, mul_assoc]
      rw [map_mul, map_apply_ι, rankOneComplement_apply, map_sub, map_smul, hp,
        CliffordAlgebra.contractLeft_ι_mul]
      simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc,
        hezero, hanti, smul_zero]
      abel

/-- Contraction vanishes on the actual exterior image of a linear map
whose composite with the functional is zero. -/
theorem contractLeft_map_eq_zero
    {N : Type*} [AddCommGroup N] [Module R N]
    (ε : M →ₗ[R] R) (f : N →ₗ[R] M) (hf : ε.comp f = 0)
    (z : ExteriorAlgebra R N) :
    CliffordAlgebra.contractLeft ε (map f z) = 0 := by
  induction z using CliffordAlgebra.left_induction with
  | algebraMap r => simp [CliffordAlgebra.contractLeft_algebraMap]
  | add z w hz hw => simp only [map_add, hz, hw, add_zero]
  | ι_mul z m hz =>
      have hm : ε (f m) = 0 := congrArg (fun q : N →ₗ[R] R => q m) hf
      rw [map_mul, map_apply_ι, CliffordAlgebra.contractLeft_ι_mul, hm, hz]
      simp

/-- The rank-one complement fixes the original contracted image. -/
theorem map_rankOneComplement_contractLeft
    (ε : M →ₗ[R] R) (e : M) (z : ExteriorAlgebra R M) :
    map (rankOneComplement R M ε e) (CliffordAlgebra.contractLeft ε z) =
      CliffordAlgebra.contractLeft ε z := by
  have h := map_rankOneComplement_add_wedge_contract R M ε e
    (CliffordAlgebra.contractLeft ε z)
  rw [CliffordAlgebra.contractLeft_contractLeft (Q := (0 : QuadraticForm R M))] at h
  simpa only [mul_zero, add_zero] using h

/-- The actual complement for the last summand of a product is the
original projection followed by inclusion. -/
theorem rankOneComplement_prod :
    rankOneComplement R (M × R) (LinearMap.snd R M R) (0, 1) =
      (LinearMap.inl R M R).comp (LinearMap.fst R M R) := by
  apply LinearMap.ext
  intro z
  apply Prod.ext <;> simp [rankOneComplement_apply]

end ExteriorAlgebra

namespace exteriorPower

universe u v

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

/-- Degreewise rank-one splitting on the original exterior powers. -/
theorem map_rankOneComplement_add_wedge_contract
    (ε : M →ₗ[R] R) (e : M) (n : ℕ) (z : ⋀[R]^(n + 1) M) :
    map (n + 1) (ExteriorAlgebra.rankOneComplement R M ε e) z +
      wedgeLeft R M e n (contractLeft R M ε n z) = z := by
  apply Subtype.ext
  simp only [Submodule.coe_add, coe_map, wedgeLeft_apply_coe, contractLeft_apply_coe]
  exact ExteriorAlgebra.map_rankOneComplement_add_wedge_contract R M ε e z

end exteriorPower
