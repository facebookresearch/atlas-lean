/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
module

public import MathlibExt.LinearAlgebra.Alternating.RestrictScalars
public import MathlibExt.LinearAlgebra.ExteriorPower.Deletion
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.LinearAlgebra.ExteriorAlgebra.BaseChange
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
public import Mathlib.RingTheory.GradedAlgebra.TensorProduct
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Base change for exterior powers

This file constructs the canonical map from the scalar extension of an
exterior power to the exterior power of the scalar extension. It is natural
for every module, commutes with deletion, and is always an equivalence. The
equivalence is the restriction of Mathlib's exterior-algebra base-change
isomorphism to the native homogeneous decomposition.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

noncomputable section

open Function
open scoped TensorProduct

universe u v w z

namespace exteriorPower

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
variable (M : Type w) [AddCommGroup M] [Module R M]

/-- A linear equivalence induces an equivalence on each exterior power. -/
def mapEquiv (n : ℕ) {N : Type z} [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) : (⋀[R]^n M) ≃ₗ[R] (⋀[R]^n N) :=
  LinearEquiv.ofLinearMap
    (map n e.toLinearMap)
    (map n e.symm.toLinearMap)
    (by ext x; simp [← map_comp])
    (by ext x; simp [← map_comp])

@[simp]
theorem mapEquiv_apply_ιMulti (n : ℕ) {N : Type z}
    [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) (a : Fin n → M) :
    mapEquiv R M n e (ιMulti R n a) = ιMulti R n (e ∘ a) := by
  exact map_apply_ιMulti e.toLinearMap a

@[simp]
theorem mapEquiv_refl (n : ℕ) :
    mapEquiv R M n (LinearEquiv.refl R M) = LinearEquiv.refl R (⋀[R]^n M) := by
  apply LinearEquiv.toLinearMap_injective
  exact map_id

theorem mapEquiv_trans (n : ℕ)
    {N : Type z} [AddCommGroup N] [Module R N]
    {P : Type*} [AddCommGroup P] [Module R P]
    (e : M ≃ₗ[R] N) (f : N ≃ₗ[R] P) :
    mapEquiv R M n (e.trans f) =
      (mapEquiv R M n e).trans (mapEquiv R N n f) := by
  apply LinearEquiv.toLinearMap_injective
  exact map_comp e.toLinearMap f.toLinearMap

private def baseChangeAlternating (n : ℕ) :
    M [⋀^Fin n]→ₗ[R] (⋀[S]^n (S ⊗[R] M)) :=
  ((ιMulti S n (M := S ⊗[R] M)).restrictScalars (R := R)).compLinearMap
    (TensorProduct.mk R S M 1)

/-- The canonical map from the scalar extension of an exterior power to the
exterior power of the scalar extension. -/
@[no_expose]
def baseChangeMap (n : ℕ) :
    S ⊗[R] (⋀[R]^n M) →ₗ[S] (⋀[S]^n (S ⊗[R] M)) :=
  TensorProduct.AlgebraTensorModule.lift
    ((LinearMap.lsmul S ((⋀[R]^n M) →ₗ[R] (⋀[S]^n (S ⊗[R] M)))).flip
      (alternatingMapLinearEquiv (baseChangeAlternating R S M n)))

@[simp]
theorem baseChangeMap_apply_tmul_ιMulti (n : ℕ) (s : S) (a : Fin n → M) :
    baseChangeMap R S M n (s ⊗ₜ[R] ιMulti R n a) =
      s • ιMulti S n (fun i => (1 : S) ⊗ₜ[R] a i) := by
  rw [baseChangeMap, TensorProduct.AlgebraTensorModule.lift_tmul]
  change s • alternatingMapLinearEquiv (baseChangeAlternating R S M n)
      (ιMulti R n a) = _
  rw [alternatingMapLinearEquiv_apply_ιMulti]
  rfl

/-- Degree-zero normalization of the canonical exterior base-change map. -/
theorem baseChangeMap_zero :
    (zeroEquiv S (S ⊗[R] M)).toLinearMap.comp
        (baseChangeMap R S M 0) =
      (TensorProduct.AlgebraTensorModule.rid R S S).toLinearMap.comp
        ((zeroEquiv R M).toLinearMap.baseChange S) := by
  apply TensorProduct.AlgebraTensorModule.curry_injective
  apply LinearMap.ext
  intro s
  apply exteriorPower.linearMap_ext
    (R := R) (n := 0) (M := M) (N := S)
  apply AlternatingMap.ext
  intro a
  change zeroEquiv S (S ⊗[R] M)
      (baseChangeMap R S M 0 (s ⊗ₜ[R] ιMulti R 0 a)) =
    TensorProduct.AlgebraTensorModule.rid R S S
      (((zeroEquiv R M).toLinearMap.baseChange S)
        (s ⊗ₜ[R] ιMulti R 0 a))
  rw [baseChangeMap_apply_tmul_ιMulti, map_smul,
    zeroEquiv_ιMulti, smul_eq_mul, mul_one]
  simp

/-- Degree-one normalization of the canonical exterior base-change map. -/
theorem baseChangeMap_one :
    (oneEquiv S (S ⊗[R] M)).toLinearMap.comp
        (baseChangeMap R S M 1) =
      (oneEquiv R M).toLinearMap.baseChange S := by
  apply TensorProduct.AlgebraTensorModule.curry_injective
  apply LinearMap.ext
  intro s
  apply exteriorPower.linearMap_ext
    (R := R) (n := 1) (M := M) (N := S ⊗[R] M)
  apply AlternatingMap.ext
  intro a
  change oneEquiv S (S ⊗[R] M)
      (baseChangeMap R S M 1 (s ⊗ₜ[R] ιMulti R 1 a)) =
    ((oneEquiv R M).toLinearMap.baseChange S)
      (s ⊗ₜ[R] ιMulti R 1 a)
  rw [baseChangeMap_apply_tmul_ιMulti, map_smul, oneEquiv_ιMulti]
  change s • ((1 : S) ⊗ₜ[R] a 0) =
    s ⊗ₜ[R] oneEquiv R M (ιMulti R 1 a)
  rw [oneEquiv_ιMulti]
  change (s * 1) ⊗ₜ[R] a 0 = s ⊗ₜ[R] a 0
  rw [mul_one]

private theorem nativeBaseChangeEquiv_tmul_ιMulti (n : ℕ) (s : S) (a : Fin n → M) :
    ExteriorAlgebra.baseChangeEquiv R M S
        (s ⊗ₜ[R] ExteriorAlgebra.ιMulti R n a) =
      s • ExteriorAlgebra.ιMulti S n (fun i => (1 : S) ⊗ₜ[R] a i) := by
  have hword : ∀ (k : ℕ) (v : Fin k → M),
      ExteriorAlgebra.baseChangeEquiv R M S
          ((1 : S) ⊗ₜ[R] ExteriorAlgebra.ιMulti R k v) =
        ExteriorAlgebra.ιMulti S k (fun i => (1 : S) ⊗ₜ[R] v i) := by
    intro k
    induction k with
    | zero =>
        intro v
        rw [ExteriorAlgebra.ιMulti_zero_apply, ExteriorAlgebra.ιMulti_zero_apply]
        change ExteriorAlgebra.baseChangeEquiv R M S (1 : S ⊗[R] ExteriorAlgebra R M) = 1
        exact map_one _
    | succ k ih =>
        intro v
        rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_succ_apply]
        rw [show (1 : S) ⊗ₜ[R]
            (ExteriorAlgebra.ι R (v 0) * ExteriorAlgebra.ιMulti R k (Matrix.vecTail v)) =
          ((1 : S) ⊗ₜ[R] ExteriorAlgebra.ι R (v 0)) *
            ((1 : S) ⊗ₜ[R] ExteriorAlgebra.ιMulti R k (Matrix.vecTail v)) by
          rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]]
        rw [map_mul, ExteriorAlgebra.baseChangeEquiv_apply, ih]
        rfl
  rw [show s ⊗ₜ[R] ExteriorAlgebra.ιMulti R n a =
      s • ((1 : S) ⊗ₜ[R] ExteriorAlgebra.ιMulti R n a) by
    simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]]
  rw [map_smul, hword]

/-- The canonical exterior-power map is the homogeneous restriction of the
native exterior-algebra base-change isomorphism. -/
theorem baseChangeMap_inclusion (n : ℕ) :
    (⋀[S]^n (S ⊗[R] M)).subtype.comp (baseChangeMap R S M n) =
      (ExteriorAlgebra.baseChangeEquiv R M S).toLinearMap.comp
        ((⋀[R]^n M).subtype.baseChange S) := by
  apply TensorProduct.AlgebraTensorModule.curry_injective
  apply LinearMap.ext
  intro s
  apply exteriorPower.linearMap_ext
    (R := R) (n := n) (M := M) (N := ExteriorAlgebra S (S ⊗[R] M))
  apply AlternatingMap.ext
  intro a
  change (baseChangeMap R S M n (s ⊗ₜ[R] ιMulti R n a) :
      ExteriorAlgebra S (S ⊗[R] M)) =
    ExteriorAlgebra.baseChangeEquiv R M S
      (s ⊗ₜ[R] ExteriorAlgebra.ιMulti R n a)
  rw [baseChangeMap_apply_tmul_ιMulti]
  change s • ExteriorAlgebra.ιMulti S n (fun i => (1 : S) ⊗ₜ[R] a i) = _
  exact (nativeBaseChangeEquiv_tmul_ιMulti R S M n s a).symm

private theorem nativeBaseChangeEquiv_symm_ι_mem (v : S ⊗[R] M) :
    (ExteriorAlgebra.baseChangeEquiv R M S).symm (ExteriorAlgebra.ι S v) ∈
      (⋀[R]^1 M).baseChange S := by
  induction v using TensorProduct.inductionOn with
  | tmul s m =>
      rw [ExteriorAlgebra.baseChangeEquiv_symm_apply]
      exact Submodule.tmul_mem_baseChange_of_mem s (by
        change ExteriorAlgebra.ι R m ∈ (LinearMap.range (ExteriorAlgebra.ι R)) ^ 1
        rw [pow_one]
        exact LinearMap.mem_range_self _ m)
  | add v z hv hz =>
      rw [map_add, map_add]
      exact Submodule.add_mem _ hv hz

private theorem nativeBaseChangeEquiv_symm_mem (n : ℕ)
    (a : ExteriorAlgebra S (S ⊗[R] M)) (ha : a ∈ ⋀[S]^n (S ⊗[R] M)) :
    (ExteriorAlgebra.baseChangeEquiv R M S).symm a ∈ (⋀[R]^n M).baseChange S := by
  change a ∈ (LinearMap.range (ExteriorAlgebra.ι S)) ^ n at ha
  induction ha using Submodule.pow_induction_on_left' with
  | algebraMap s =>
      rw [AlgEquiv.commutes, Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ s
        (SetLike.one_mem_graded (fun k : ℕ => (⋀[R]^k M).baseChange S))
  | add _ _ _ _ _ ha hb =>
      rw [map_add]
      exact Submodule.add_mem _ ha hb
  | mem_mul _ hm _ _ _ ih =>
      obtain ⟨v, rfl⟩ := hm
      rw [map_mul]
      simpa only [Nat.add_comm] using
        SetLike.mul_mem_graded (A := fun k : ℕ => (⋀[R]^k M).baseChange S)
          (nativeBaseChangeEquiv_symm_ι_mem R S M v) ih

private theorem nativeBaseChangeEquiv_map_degree (n : ℕ) :
    ((⋀[R]^n M).baseChange S).map
        (ExteriorAlgebra.baseChangeEquiv R M S).toLinearMap =
      ⋀[S]^n (S ⊗[R] M) := by
  apply le_antisymm
  · rintro _ ⟨a, ha, rfl⟩
    rw [Submodule.baseChange] at ha
    obtain ⟨t, rfl⟩ := ha
    have h := LinearMap.congr_fun (baseChangeMap_inclusion R S M n) t
    rw [LinearMap.comp_apply, LinearMap.comp_apply, Submodule.subtype_apply] at h
    rw [← h]
    exact (baseChangeMap R S M n t).property
  · intro a ha
    exact ⟨(ExteriorAlgebra.baseChangeEquiv R M S).symm a,
      nativeBaseChangeEquiv_symm_mem R S M n a ha,
      (ExteriorAlgebra.baseChangeEquiv R M S).apply_symm_apply a⟩

private def nativeDegreeBaseChangeEquiv (n : ℕ) :
    S ⊗[R] (⋀[R]^n M) ≃ₗ[S] (⋀[S]^n (S ⊗[R] M)) :=
  (LinearEquiv.ofBijective ((⋀[R]^n M).toBaseChange S)
      (DirectSum.toBaseChange_bijective (S := S) (fun k : ℕ => ⋀[R]^k M) n)).trans
    ((ExteriorAlgebra.baseChangeEquiv R M S).toLinearEquiv.ofSubmodules
      ((⋀[R]^n M).baseChange S) (⋀[S]^n (S ⊗[R] M))
      (nativeBaseChangeEquiv_map_degree R S M n))

private theorem nativeDegreeBaseChangeEquiv_toLinearMap (n : ℕ) :
    (nativeDegreeBaseChangeEquiv R S M n).toLinearMap = baseChangeMap R S M n := by
  apply TensorProduct.AlgebraTensorModule.curry_injective
  apply LinearMap.ext
  intro s
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  change (nativeDegreeBaseChangeEquiv R S M n (s ⊗ₜ[R] a) :
      ExteriorAlgebra S (S ⊗[R] M)) =
    (baseChangeMap R S M n (s ⊗ₜ[R] a) : ExteriorAlgebra S (S ⊗[R] M))
  have h : (nativeDegreeBaseChangeEquiv R S M n (s ⊗ₜ[R] a) :
      ExteriorAlgebra S (S ⊗[R] M)) =
      ExteriorAlgebra.baseChangeEquiv R M S (s ⊗ₜ[R] (a : ExteriorAlgebra R M)) := by
    rw [nativeDegreeBaseChangeEquiv, LinearEquiv.trans_apply,
      LinearEquiv.ofSubmodules_apply]
    change ExteriorAlgebra.baseChangeEquiv R M S
        (((⋀[R]^n M).toBaseChange S (s ⊗ₜ[R] a) : S ⊗[R] ExteriorAlgebra R M)) = _
    rw [Submodule.coe_toBaseChange_tmul]
  rw [h]
  simpa only [LinearMap.comp_apply, LinearMap.baseChange_tmul,
    Submodule.subtype_apply, AlgEquiv.toLinearMap_apply] using
    (LinearMap.congr_fun (baseChangeMap_inclusion R S M n) (s ⊗ₜ[R] a)).symm

private theorem baseChangeMap_bijective (n : ℕ) :
    Function.Bijective (baseChangeMap R S M n) := by
  rw [← nativeDegreeBaseChangeEquiv_toLinearMap R S M n]
  exact (nativeDegreeBaseChangeEquiv R S M n).bijective

/-- Exterior powers commute with arbitrary extension of scalars. The
forward map is canonical and no basis or flatness hypothesis is needed. -/
@[no_expose]
def baseChangeEquiv (n : ℕ) :
    S ⊗[R] (⋀[R]^n M) ≃ₗ[S] (⋀[S]^n (S ⊗[R] M)) :=
  LinearEquiv.ofBijective (baseChangeMap R S M n)
    (baseChangeMap_bijective R S M n)

/-- The equivalence has the original canonical map as its forward linear map. -/
@[simp]
theorem baseChangeEquiv_toLinearMap (n : ℕ) :
    (baseChangeEquiv R S M n).toLinearMap = baseChangeMap R S M n := by
  apply LinearMap.ext
  intro p
  rfl

@[simp]
theorem baseChangeEquiv_apply_tmul_ιMulti
    (n : ℕ) (s : S) (a : Fin n → M) :
    baseChangeEquiv R S M n (s ⊗ₜ[R] ιMulti R n a) =
      s • ιMulti S n (fun i => (1 : S) ⊗ₜ[R] a i) :=
  baseChangeMap_apply_tmul_ιMulti R S M n s a

/-- The inverse equivalence recovers the actual scalar-extended exterior word. -/
@[simp↓]
theorem baseChangeEquiv_symm_apply_smul_ιMulti
    (n : ℕ) (s : S) (a : Fin n → M) :
    (baseChangeEquiv R S M n).symm
        (s • ιMulti S n (fun i => (1 : S) ⊗ₜ[R] a i)) =
      s ⊗ₜ[R] ιMulti R n a := by
  rw [← baseChangeEquiv_apply_tmul_ιMulti R S M n s a]
  exact (baseChangeEquiv R S M n).symm_apply_apply _

/-- The inverse on an unscaled exterior word is the actual tensor of that word. -/
@[simp]
theorem baseChangeEquiv_symm_apply_ιMulti (n : ℕ) (a : Fin n → M) :
    (baseChangeEquiv R S M n).symm
        (ιMulti S n (fun i => (1 : S) ⊗ₜ[R] a i)) =
      (1 : S) ⊗ₜ[R] ιMulti R n a := by
  simpa only [one_smul] using
    baseChangeEquiv_symm_apply_smul_ιMulti R S M n (1 : S) a

/-- In degree zero the exterior base-change equivalence is the canonical
scalar-extension identification. -/
theorem baseChangeEquiv_zero :
    (baseChangeEquiv R S M 0).trans (zeroEquiv S (S ⊗[R] M)) =
      ((zeroEquiv R M).baseChange R S _ _).trans
        (TensorProduct.AlgebraTensorModule.rid R S S) := by
  apply LinearEquiv.toLinearMap_injective
  exact baseChangeMap_zero R S M

/-- In degree one the exterior base-change equivalence is the base change of
the canonical degree-one equivalence. -/
theorem baseChangeEquiv_one :
    (baseChangeEquiv R S M 1).trans (oneEquiv S (S ⊗[R] M)) =
      (oneEquiv R M).baseChange R S _ _ := by
  apply LinearEquiv.toLinearMap_injective
  exact baseChangeMap_one R S M

/-- Naturality of the canonical exterior base-change map. -/
theorem baseChangeMap_naturality
    {N : Type z} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (n : ℕ) :
    baseChangeMap R S N n ∘ₗ (map n f).baseChange S =
      map n (f.baseChange S) ∘ₗ baseChangeMap R S M n := by
  apply TensorProduct.AlgebraTensorModule.curry_injective
  apply LinearMap.ext
  intro s
  apply exteriorPower.linearMap_ext
    (R := R) (n := n) (M := M) (N := ⋀[S]^n (S ⊗[R] N))
  apply AlternatingMap.ext
  intro a
  change baseChangeMap R S N n
      (s ⊗ₜ[R] map n f (ιMulti R n a)) =
    map n (f.baseChange S)
      (baseChangeMap R S M n (s ⊗ₜ[R] ιMulti R n a))
  rw [map_apply_ιMulti, baseChangeMap_apply_tmul_ιMulti,
    baseChangeMap_apply_tmul_ιMulti, map_smul, map_apply_ιMulti]
  congr 2

/-- Exterior-power deletion commutes with scalar extension. -/
theorem baseChangeMap_deletion (n : ℕ) :
    (exteriorPower.deletion S (S ⊗[R] M) n).comp
        (baseChangeMap R S M (n + 1)) =
      (TensorProduct.map (baseChangeMap R S M n)
          (LinearMap.id (R := S) (M := S ⊗[R] M))).comp
        ((TensorProduct.AlgebraTensorModule.distribBaseChange
            R S (⋀[R]^n M) M).toLinearMap.comp
          ((exteriorPower.deletion R M n).baseChange S)) := by
  apply TensorProduct.AlgebraTensorModule.curry_injective
  apply LinearMap.ext
  intro s
  apply exteriorPower.linearMap_ext
    (R := R) (n := n + 1) (M := M)
      (N := (⋀[S]^n (S ⊗[R] M)) ⊗[S] (S ⊗[R] M))
  apply AlternatingMap.ext
  intro a
  change exteriorPower.deletion S (S ⊗[R] M) n
      (baseChangeMap R S M (n + 1)
        (s ⊗ₜ[R] exteriorPower.ιMulti R (n + 1) a)) =
    TensorProduct.map (baseChangeMap R S M n)
        (LinearMap.id (R := S) (M := S ⊗[R] M))
      (TensorProduct.AlgebraTensorModule.distribBaseChange
        R S (⋀[R]^n M) M
          (((exteriorPower.deletion R M n).baseChange S)
            (s ⊗ₜ[R] exteriorPower.ιMulti R (n + 1) a)))
  rw [baseChangeMap_apply_tmul_ιMulti, map_smul,
    exteriorPower.deletion_apply_ιMulti]
  simp only [LinearMap.baseChange_tmul,
    exteriorPower.deletion_apply_ιMulti, map_sum, TensorProduct.tmul_sum,
    Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hbalance :
      s ⊗ₜ[R] (((-1 : R) ^ i.val) •
        ((exteriorPower.ιMulti R n (a ∘ i.succAbove)) ⊗ₜ[R] a i)) =
      (algebraMap R S ((-1 : R) ^ i.val) * s) ⊗ₜ[R]
        ((exteriorPower.ιMulti R n (a ∘ i.succAbove)) ⊗ₜ[R] a i) := by
    rw [TensorProduct.tmul_smul]
    rw [← IsScalarTower.algebraMap_smul S ((-1 : R) ^ i.val)]
    rw [TensorProduct.smul_tmul']
    rw [smul_eq_mul]
  rw [hbalance, TensorProduct.AlgebraTensorModule.distribBaseChange_tmul,
    TensorProduct.map_tmul, LinearMap.id_apply,
    baseChangeMap_apply_tmul_ιMulti]
  simp [TensorProduct.smul_tmul', smul_smul, mul_comm]
  congr 2

end exteriorPower
