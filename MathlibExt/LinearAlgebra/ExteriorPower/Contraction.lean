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

public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import MathlibExt.LinearAlgebra.ExteriorPower.Deletion

/-!
# Contraction on exterior powers

Mathlib's `CliffordAlgebra.contractLeft`, specialized to the zero quadratic
form, is contraction on the exterior algebra. This file proves its pure-word
formula and homogeneous degree behavior, restricts it to consecutive exterior
powers, and records square-zero, anticommutation, naturality, and compatibility
with the existing exterior-power deletion map.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open Function

universe u v w

namespace ExteriorAlgebra

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

/-- Contraction by a linear functional on a decomposable exterior word. -/
theorem contractLeft_ιMulti (x : Module.Dual R M) (n : ℕ)
    (a : Fin (n + 1) → M) :
    CliffordAlgebra.contractLeft x (ιMulti R (n + 1) a) =
      ∑ i : Fin (n + 1), (-1 : R) ^ i.val •
        (x (a i) • ιMulti R n (a ∘ i.succAbove)) := by
  induction n with
  | zero =>
      rw [ιMulti_succ_apply, CliffordAlgebra.contractLeft_ι_mul,
        Fin.sum_univ_one]
      simp
  | succ n ih =>
      rw [ιMulti_succ_apply, CliffordAlgebra.contractLeft_ι_mul, ih]
      conv_rhs => rw [Fin.sum_univ_succ]
      have hhead : a ∘ (0 : Fin (n + 2)).succAbove = Matrix.vecTail a := by
        funext j
        rw [Function.comp_apply, Fin.zero_succAbove]
        rfl
      simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ]
      rw [hhead, sub_eq_add_neg]
      congr 1
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      have hdelete : a ∘ i.succ.succAbove =
          Matrix.vecCons (a 0) (Matrix.vecTail a ∘ i.succAbove) := by
        funext j
        refine Fin.cases ?_ (fun k => ?_) j
        · simp only [Function.comp_apply, Fin.succ_succAbove_zero, Matrix.cons_val_zero]
        · simp only [Function.comp_apply, Fin.succ_succAbove_succ, Matrix.cons_val_succ]
          rfl
      rw [hdelete, ιMulti_succ_apply]
      simp only [Matrix.cons_val_zero, Matrix.vecTail, Function.comp_apply,
        pow_succ, mul_neg, mul_one, neg_smul, mul_smul_comm]
      congr 3

/-- Contraction lowers a positive homogeneous exterior degree by one. -/
theorem contractLeft_mem_exteriorPower (x : Module.Dual R M) (n : ℕ)
    (a : ExteriorAlgebra R M) (ha : a ∈ ⋀[R]^(n + 1) M) :
    CliffordAlgebra.contractLeft x a ∈ ⋀[R]^n M := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree R (n + 1)] at ha
  refine Submodule.span_induction
    (p := fun a _ ↦ CliffordAlgebra.contractLeft x a ∈ ⋀[R]^n M) ?_ ?_ ?_ ?_ ha
  · rintro _ ⟨v, rfl⟩
    rw [contractLeft_ιMulti R M x n v]
    exact Submodule.sum_mem _ fun i _ ↦
      Submodule.smul_mem _ _ (Submodule.smul_mem _ _
        (ExteriorAlgebra.ιMulti_range R n (Set.mem_range_self _)))
  · simpa only [map_zero] using (Submodule.zero_mem (⋀[R]^n M))
  · intro a b _ _ ha hb
    simpa only [map_add] using Submodule.add_mem (⋀[R]^n M) ha hb
  · intro r a _ ha
    simpa only [map_smul] using Submodule.smul_mem (⋀[R]^n M) r ha

end ExteriorAlgebra

namespace exteriorPower

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

/-- Contraction by a linear functional, restricted from exterior degree
`n + 1` to exterior degree `n`. -/
def contractLeft (x : Module.Dual R M) (n : ℕ) :
    (⋀[R]^(n + 1) M) →ₗ[R] (⋀[R]^n M) :=
  (CliffordAlgebra.contractLeft x).restrict
    (ExteriorAlgebra.contractLeft_mem_exteriorPower R M x n)

/-- The underlying exterior-algebra value of degree-restricted contraction. -/
@[simp]
theorem contractLeft_apply_coe (x : Module.Dual R M) (n : ℕ)
    (a : ⋀[R]^(n + 1) M) :
    (contractLeft R M x n a : ExteriorAlgebra R M) =
      CliffordAlgebra.contractLeft x a :=
  rfl

/-- Degree-restricted contraction is linear in the contracting functional. -/
def contractLeftLinear (n : ℕ) :
    Module.Dual R M →ₗ[R]
      ((⋀[R]^(n + 1) M) →ₗ[R] (⋀[R]^n M)) where
  toFun x := contractLeft R M x n
  map_add' x y := by
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    change CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) (x + y)
        (a : ExteriorAlgebra R M) =
      CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) x
          (a : ExteriorAlgebra R M) +
        CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) y
          (a : ExteriorAlgebra R M)
    simp only [map_add, LinearMap.add_apply]
  map_smul' r x := by
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    change CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) (r • x)
        (a : ExteriorAlgebra R M) =
      r • CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) x
        (a : ExteriorAlgebra R M)
    simp only [map_smul, LinearMap.smul_apply]

/-- Evaluating the bundled degree-restricted contraction recovers
`contractLeft`. -/
theorem contractLeftLinear_apply (n : ℕ) (x : Module.Dual R M) :
    contractLeftLinear R M n x = contractLeft R M x n :=
  rfl

/-- Contraction by the zero functional is zero. -/
@[simp]
theorem contractLeft_zero (n : ℕ) :
    contractLeft R M (0 : Module.Dual R M) n = 0 :=
  map_zero (contractLeftLinear R M n)

/-- Contraction by a sum is the sum of contractions. -/
@[simp]
theorem contractLeft_add (x y : Module.Dual R M) (n : ℕ) :
    contractLeft R M (x + y) n =
      contractLeft R M x n + contractLeft R M y n :=
  map_add (contractLeftLinear R M n) x y

/-- Contraction is compatible with scalar multiplication of the functional. -/
@[simp]
theorem contractLeft_smul (r : R) (x : Module.Dual R M) (n : ℕ) :
    contractLeft R M (r • x) n = r • contractLeft R M x n :=
  map_smul (contractLeftLinear R M n) r x

/-- Signed pure-word formula for degree-restricted contraction. -/
theorem contractLeft_apply_ιMulti (x : Module.Dual R M) (n : ℕ)
    (a : Fin (n + 1) → M) :
    contractLeft R M x n (ιMulti R (n + 1) a) =
      ∑ i : Fin (n + 1), (-1 : R) ^ i.val •
        (x (a i) • ιMulti R n (a ∘ i.succAbove)) := by
  apply Subtype.ext
  simpa only [contractLeft_apply_coe, ιMulti_apply_coe, SetLike.val_smul_of_tower,
    Submodule.coe_sum] using ExteriorAlgebra.contractLeft_ιMulti R M x n a

/-- Evaluating the removed factor of `exteriorPower.deletion` by `x` is
degree-restricted contraction. -/
theorem contractLeft_eq_deletion (x : Module.Dual R M) (n : ℕ) :
    contractLeft R M x n =
      (TensorProduct.rid R (⋀[R]^n M)).toLinearMap.comp
        ((TensorProduct.map (LinearMap.id (R := R) (M := (⋀[R]^n M))) x).comp
          (deletion R M n)) := by
  apply exteriorPower.linearMap_ext
    (R := R) (n := n + 1) (M := M) (N := ⋀[R]^n M)
  apply AlternatingMap.ext
  intro a
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply]
  rw [contractLeft_apply_ιMulti, deletion_apply_ιMulti]
  simp only [map_sum, map_smul, TensorProduct.map_tmul, LinearMap.id_apply,
    LinearEquiv.coe_coe, TensorProduct.rid_tmul]

/-- Successive contractions by the same functional compose to zero. -/
theorem contractLeft_comp_contractLeft (x : Module.Dual R M) (n : ℕ) :
    (contractLeft R M x n).comp (contractLeft R M x (n + 1)) = 0 := by
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  exact CliffordAlgebra.contractLeft_contractLeft (Q := (0 : QuadraticForm R M)) x
    (a : ExteriorAlgebra R M)

/-- Contractions by two functionals anticommute. -/
theorem contractLeft_anticomm (x y : Module.Dual R M) (n : ℕ) :
    (contractLeft R M x n).comp (contractLeft R M y (n + 1)) =
      -((contractLeft R M y n).comp (contractLeft R M x (n + 1))) := by
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  exact CliffordAlgebra.contractLeft_comm (Q := (0 : QuadraticForm R M)) x y
    (a : ExteriorAlgebra R M)

/-- Degree-restricted contraction is natural under a linear map compatible
with the two functionals. -/
theorem contractLeft_naturality
    {N : Type w} [AddCommGroup N] [Module R N]
    (x : Module.Dual R M) (y : Module.Dual R N) (f : M →ₗ[R] N)
    (hxy : y.comp f = x) (n : ℕ) :
    (contractLeft R N y n).comp (map (n + 1) f) =
      (map n f).comp (contractLeft R M x n) := by
  apply exteriorPower.linearMap_ext
    (R := R) (n := n + 1) (M := M) (N := ⋀[R]^n N)
  apply AlternatingMap.ext
  intro a
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
    map_apply_ιMulti, contractLeft_apply_ιMulti, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro i _
  have hcoeff : y (f (a i)) = x (a i) := LinearMap.congr_fun hxy (a i)
  simp only [Function.comp_apply]
  rw [hcoeff]
  rfl

/-- In degrees one and zero, contraction is the original functional under
the canonical exterior-power equivalences. -/
theorem zeroEquiv_comp_contractLeft (x : Module.Dual R M) :
    (zeroEquiv R M).toLinearMap.comp (contractLeft R M x 0) =
      x.comp (oneEquiv R M).toLinearMap := by
  apply exteriorPower.linearMap_ext
    (R := R) (n := 1) (M := M) (N := R)
  apply AlternatingMap.ext
  intro a
  simp [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
    contractLeft_apply_ιMulti]

end exteriorPower
