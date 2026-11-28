/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.ExteriorAlgebra.OfAlternating
public import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation

/-!
# Canonical exterior-degree projections

The native alternating universal property of the entire exterior algebra
defines the projection to one homogeneous degree. Its restriction is the
identity in that degree and zero in every other degree. The construction is
basis independent and natural in arbitrary linear maps.
-/

@[expose] public section

noncomputable section

universe u v w

namespace exteriorPower

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

private def projectionAlternating (n k : ℕ) : M [⋀^Fin k]→ₗ[R] (⋀[R]^n M) :=
  if h : k = n then (ιMulti R n).domDomCongr (finCongr h.symm) else 0

/-- The canonical projection from the exterior algebra to exterior degree `n`. -/
def projection (n : ℕ) : ExteriorAlgebra R M →ₗ[R] (⋀[R]^n M) :=
  private_decl% (ExteriorAlgebra.liftAlternating (projectionAlternating R M n))

@[simp]
theorem projection_ιMulti_self (n : ℕ) (v : Fin n → M) :
    projection R M n (ExteriorAlgebra.ιMulti R n v) = ιMulti R n v := by
  change ExteriorAlgebra.liftAlternating (projectionAlternating R M n)
    (ExteriorAlgebra.ιMulti R n v) = _
  rw [ExteriorAlgebra.liftAlternating_apply_ιMulti]
  simp only [projectionAlternating, dif_pos rfl]
  rfl

theorem projection_ιMulti_ne (n k : ℕ) (h : k ≠ n) (v : Fin k → M) :
    projection R M n (ExteriorAlgebra.ιMulti R k v) = 0 := by
  change ExteriorAlgebra.liftAlternating (projectionAlternating R M n)
    (ExteriorAlgebra.ιMulti R k v) = _
  simp only [ExteriorAlgebra.liftAlternating_apply_ιMulti, projectionAlternating,
    dif_neg h, AlternatingMap.zero_apply]

/-- The degree projection is a retraction of its actual homogeneous inclusion. -/
theorem projection_comp_subtype (n : ℕ) :
    (projection R M n).comp (⋀[R]^n M).subtype = LinearMap.id := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
    Submodule.subtype_apply, ιMulti_apply_coe, projection_ιMulti_self, LinearMap.id_apply]

@[simp]
theorem projection_subtype_apply (n : ℕ) (a : ⋀[R]^n M) :
    projection R M n (a : ExteriorAlgebra R M) = a :=
  LinearMap.congr_fun (projection_comp_subtype R M n) a

/-- Every other homogeneous degree is killed. -/
theorem projection_comp_subtype_ne (n k : ℕ) (h : k ≠ n) :
    (projection R M n).comp (⋀[R]^k M).subtype = 0 := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
    Submodule.subtype_apply, ιMulti_apply_coe, projection_ιMulti_ne R M n k h,
    LinearMap.zero_apply]

theorem projection_eq_zero_of_mem (n k : ℕ) (h : k ≠ n)
    (a : ExteriorAlgebra R M) (ha : a ∈ ⋀[R]^k M) : projection R M n a = 0 :=
  LinearMap.congr_fun (projection_comp_subtype_ne R M n k h) ⟨a, ha⟩

/-- The native grade involution on an exterior word has its expected sign. -/
theorem involute_ιMulti (n : ℕ) (v : Fin n → M) :
    CliffordAlgebra.involute (ExteriorAlgebra.ιMulti R n v) =
      (-1 : R) ^ n • ExteriorAlgebra.ιMulti R n v := by
  induction n with
  | zero =>
      simp only [ExteriorAlgebra.ιMulti_zero_apply, map_one, pow_zero, one_smul]
  | succ n ih =>
      simp only [ExteriorAlgebra.ιMulti_succ_apply, map_mul,
        CliffordAlgebra.involute_ι, ih]
      rw [mul_smul_comm, neg_mul, pow_succ, ← smul_smul, neg_one_smul]

/-- The degree projection of the grade involution has sign `(-1)^n`. -/
theorem projection_involute (n : ℕ) (a : ExteriorAlgebra R M) :
    projection R M n (CliffordAlgebra.involute a) = (-1 : R) ^ n • projection R M n a := by
  have h : (projection R M n).comp
      (CliffordAlgebra.involute : ExteriorAlgebra R M →ₐ[R] ExteriorAlgebra R M).toLinearMap =
      (-1 : R) ^ n • projection R M n := by
    apply ExteriorAlgebra.lhom_ext
    intro k
    apply AlternatingMap.ext
    intro v
    by_cases hk : k = n
    · subst k
      simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
        AlgHom.toLinearMap_apply, involute_ιMulti, map_smul,
        projection_ιMulti_self, LinearMap.smul_apply]
    · simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
        AlgHom.toLinearMap_apply, involute_ιMulti, map_smul,
        projection_ιMulti_ne R M n k hk, smul_zero, LinearMap.smul_apply]
  exact LinearMap.congr_fun h a

section Naturality

variable {N : Type w} [AddCommGroup N] [Module R N]

/-- Degree projections commute with the native exterior map in all module universes. -/
theorem projection_naturality (n : ℕ) (f : M →ₗ[R] N) :
    (projection R N n).comp (ExteriorAlgebra.map f).toLinearMap =
      (map n f).comp (projection R M n) := by
  have hmap (k : ℕ) (v : Fin k → M) :
      ExteriorAlgebra.map f (ExteriorAlgebra.ιMulti R k v) =
        ExteriorAlgebra.ιMulti R k (f ∘ v) := by
    simpa only [coe_map, ιMulti_apply_coe] using
      congrArg Subtype.val (map_apply_ιMulti f v)
  apply ExteriorAlgebra.lhom_ext
  intro k
  apply AlternatingMap.ext
  intro v
  by_cases hk : k = n
  · subst k
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      AlgHom.toLinearMap_apply, hmap, projection_ιMulti_self, map_apply_ιMulti]
  · simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      AlgHom.toLinearMap_apply, hmap, projection_ιMulti_ne R N n k hk,
      projection_ιMulti_ne R M n k hk, map_zero]

end Naturality

end exteriorPower
