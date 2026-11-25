/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.LinearAlgebra.TensorProduct.Balanced
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.TensorProduct.Associator

/-!
# Focused clients of the balanced tensor product

The model is noncommutative: the ground ring is `ℚ`, the acting ring is
`R = Matrix (Fin 2) (Fin 2) ℚ`, and `R` is both the right module (`op r • m = m * r`) and the
left module. The matrix units `e₀₀ e₀₁ e₁₀ e₁₁` make the right action differ from the left one,
so the balancing relation is not already true in `R ⊗[ℚ] R`.

* `mk e₀₁ e₁₀ = mk e₀₀ e₀₀` holds in the quotient, while the pure tensors `e₀₁ ⊗ₜ e₁₀` and
  `e₀₀ ⊗ₜ e₀₀` are separated by a ground-bilinear entry probe, which is itself not balanced.
* That class is nonzero: the descent of multiplication sends it to `e₀₀`.
* `map` of left multiplication by `e₁₀` and right multiplication by `e₀₁` moves it to the
  nonzero class `mk e₁₁ e₁₁`; `hom_ext` proves that this map intertwines the descent of
  multiplication with two-sided multiplication, which needs associativity.
* Free-action cancellation computes `cancelEquiv (mk e₀₀ (e₀₁ ⊗ₜ 1)) = e₀₁ ⊗ₜ 1`, which is
  nonzero and differs from `e₀₀ ⊗ₜ 1`. Its inverse yields the quotient identity
  `mk e₀₀ (e₀₁ ⊗ₜ 1) = mk e₀₁ (1 ⊗ₜ 1)` between pure tensors that differ before the quotient.

The file covers the quotient constructor, `balance`, `lift`/`lift_mk`, `hom_ext`,
`map`/`map_mk`, and the free-action cancellation equivalence with both round trips. It does not
cover `congr`, `map_id`, or the outer actions of `Balanced.Actions`.
-/

open scoped TensorProduct
open MulOpposite

namespace MathlibExtTest.Algebra.Homology.BalancedTensorFocusedClients

/-- The noncommutative acting ring. -/
abbrev R : Type := Matrix (Fin 2) (Fin 2) ℚ

/-- The matrix unit `E₀₀`. -/
def e₀₀ : R := !![1, 0; 0, 0]

/-- The matrix unit `E₀₁`. -/
def e₀₁ : R := !![0, 1; 0, 0]

/-- The matrix unit `E₁₀`. -/
def e₁₀ : R := !![0, 0; 1, 0]

/-- The matrix unit `E₁₁`. -/
def e₁₁ : R := !![0, 0; 0, 1]

theorem e₀₀_mul_e₀₁ : e₀₀ * e₀₁ = e₀₁ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e₀₀, e₀₁, Matrix.mul_apply, Fin.sum_univ_two]

theorem e₀₁_mul_e₁₀ : e₀₁ * e₁₀ = e₀₀ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e₀₁, e₁₀, e₀₀, Matrix.mul_apply, Fin.sum_univ_two]

theorem e₁₀_mul_e₀₁ : e₁₀ * e₀₁ = e₁₁ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e₁₀, e₀₁, e₁₁, Matrix.mul_apply, Fin.sum_univ_two]

theorem e₁₁_mul_e₁₁ : e₁₁ * e₁₁ = e₁₁ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e₁₁, Matrix.mul_apply, Fin.sum_univ_two]

theorem e₀₁_mul_e₀₀ : e₀₁ * e₀₀ = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e₀₁, e₀₀, Matrix.mul_apply, Fin.sum_univ_two]

theorem e₀₀_ne_zero : e₀₀ ≠ 0 := by
  intro h
  have h₁ := congrFun (congrFun h 0) 0
  simp [e₀₀] at h₁

theorem e₀₁_ne_zero : e₀₁ ≠ 0 := by
  intro h
  have h₁ := congrFun (congrFun h 0) 1
  simp [e₀₁] at h₁

theorem e₁₁_ne_zero : e₁₁ ≠ 0 := by
  intro h
  have h₁ := congrFun (congrFun h 1) 1
  simp [e₁₁] at h₁

theorem e₀₁_ne_e₀₀ : e₀₁ ≠ e₀₀ := by
  intro h
  have h₁ := congrFun (congrFun h 0) 0
  simp [e₀₁, e₀₀] at h₁

theorem e₁₁_ne_e₀₀ : e₁₁ ≠ e₀₀ := by
  intro h
  have h₁ := congrFun (congrFun h 0) 0
  simp [e₁₁, e₀₀] at h₁

/-- The right action is not the left action: `op e₀₁ • e₀₀ = e₀₁` but `e₀₁ • e₀₀ = 0`. -/
theorem op_smul_ne_smul : op e₀₁ • e₀₀ ≠ e₀₁ • e₀₀ := by
  rw [op_smul_eq_mul, smul_eq_mul, e₀₀_mul_e₀₁, e₀₁_mul_e₀₀]
  exact e₀₁_ne_zero

/-! ### The balancing relation identifies tensors that differ before the quotient -/

/-- The ground-bilinear entry probe `(a, b) ↦ a i j * b k l`. -/
def entryBil (i j k l : Fin 2) : R →ₗ[ℚ] R →ₗ[ℚ] ℚ :=
  LinearMap.mk₂ ℚ (fun a b => a i j * b k l)
    (by intro a₁ a₂ b; simp only [Matrix.add_apply, add_mul])
    (by intro c a b; simp only [Matrix.smul_apply, smul_eq_mul, mul_assoc])
    (by intro a b₁ b₂; simp only [Matrix.add_apply, mul_add])
    (by intro c a b; simp only [Matrix.smul_apply, smul_eq_mul, mul_left_comm])

/-- The entry probe on the unquotiented ground tensor product. -/
def entryProbe (i j k l : Fin 2) : R ⊗[ℚ] R →ₗ[ℚ] ℚ :=
  TensorProduct.lift (entryBil i j k l)

theorem entryProbe_tmul (i j k l : Fin 2) (a b : R) :
    entryProbe i j k l (a ⊗ₜ[ℚ] b) = a i j * b k l := by
  simp [entryProbe, entryBil]

/-- The two sides of the balancing relation at `(r, m, n) = (e₀₁, e₀₀, e₁₀)` are different
elements of `R ⊗[ℚ] R`. -/
theorem unquotiented_sides_ne :
    (op e₀₁ • e₀₀) ⊗ₜ[ℚ] e₁₀ ≠ e₀₀ ⊗ₜ[ℚ] (e₀₁ • e₁₀) := by
  rw [op_smul_eq_mul, smul_eq_mul, e₀₀_mul_e₀₁, e₀₁_mul_e₁₀]
  intro h
  have h₁ := congrArg (entryProbe 0 1 1 0) h
  simp [entryProbe_tmul, e₀₁, e₁₀, e₀₀] at h₁

/-- The entry probe is not balanced, so it does not descend to the quotient. -/
theorem entryBil_not_balanced :
    ¬ ∀ (r m n : R), entryBil 0 1 1 0 (op r • m) n = entryBil 0 1 1 0 m (r • n) := by
  intro h
  have h₁ := h e₀₁ e₀₀ e₁₀
  rw [op_smul_eq_mul, smul_eq_mul, e₀₀_mul_e₀₁, e₀₁_mul_e₁₀] at h₁
  simp [entryBil, e₀₁, e₁₀, e₀₀] at h₁

/-- In the balanced quotient the two classes agree. -/
theorem mk_e₀₁_e₁₀ :
    TensorProduct.Balanced.mk ℚ R R R e₀₁ e₁₀ = TensorProduct.Balanced.mk ℚ R R R e₀₀ e₀₀ := by
  have h := TensorProduct.Balanced.balance ℚ R R R e₀₁ e₀₀ e₁₀
  rwa [op_smul_eq_mul, smul_eq_mul, e₀₀_mul_e₀₁, e₀₁_mul_e₁₀] at h

/-! ### Descent of multiplication -/

/-- Multiplication, as a ground-bilinear map. -/
def mulBil : R →ₗ[ℚ] R →ₗ[ℚ] R :=
  LinearMap.mk₂ ℚ (· * ·) add_mul smul_mul_assoc mul_add mul_smul_comm

/-- Multiplication is balanced because it is associative. -/
theorem mulBil_balanced (r m n : R) : mulBil (op r • m) n = mulBil m (r • n) := by
  simp only [mulBil, LinearMap.mk₂_apply, op_smul_eq_mul, smul_eq_mul, mul_assoc]

/-- The descent of multiplication to the balanced quotient. -/
def mulLift : TensorProduct.Balanced ℚ R R R →ₗ[ℚ] R :=
  TensorProduct.Balanced.lift mulBil mulBil_balanced

theorem mulLift_mk (m n : R) :
    mulLift (TensorProduct.Balanced.mk ℚ R R R m n) = m * n := by
  rw [mulLift, TensorProduct.Balanced.lift_mk, mulBil, LinearMap.mk₂_apply]

/-- `lift_mk` computes a nonzero value. -/
theorem mulLift_mk_e₀₁_e₁₀ : mulLift (TensorProduct.Balanced.mk ℚ R R R e₀₁ e₁₀) = e₀₀ := by
  rw [mulLift_mk, e₀₁_mul_e₁₀]

/-- The identified class is nonzero, so the identification is not a collapse. -/
theorem mk_e₀₁_e₁₀_ne_zero : TensorProduct.Balanced.mk ℚ R R R e₀₁ e₁₀ ≠ 0 := by
  intro h
  have h₁ := mulLift_mk_e₀₁_e₁₀
  rw [h, map_zero] at h₁
  exact e₀₀_ne_zero h₁.symm

/-! ### Induced maps -/

/-- Left multiplication by `e₁₀` commutes with the right action. -/
theorem mulLeft_equivariant (r m : R) :
    LinearMap.mulLeft ℚ e₁₀ (op r • m) = op r • LinearMap.mulLeft ℚ e₁₀ m := by
  simp only [LinearMap.mulLeft_apply, op_smul_eq_mul, mul_assoc]

/-- Right multiplication by `e₀₁` commutes with the left action. -/
theorem mulRight_equivariant (r n : R) :
    LinearMap.mulRight ℚ e₀₁ (r • n) = r • LinearMap.mulRight ℚ e₀₁ n := by
  simp only [LinearMap.mulRight_apply, smul_eq_mul, mul_assoc]

/-- The quotient map induced by `m ↦ e₁₀ * m` and `n ↦ n * e₀₁`. -/
def sandwich : TensorProduct.Balanced ℚ R R R →ₗ[ℚ] TensorProduct.Balanced ℚ R R R :=
  TensorProduct.Balanced.map (LinearMap.mulLeft ℚ e₁₀) (LinearMap.mulRight ℚ e₀₁)
    mulLeft_equivariant mulRight_equivariant

/-- `map_mk` on a nonzero class with non-identity maps. -/
theorem sandwich_mk_e₀₁_e₁₀ :
    sandwich (TensorProduct.Balanced.mk ℚ R R R e₀₁ e₁₀) =
      TensorProduct.Balanced.mk ℚ R R R e₁₁ e₁₁ := by
  rw [sandwich, TensorProduct.Balanced.map_mk, LinearMap.mulLeft_apply,
    LinearMap.mulRight_apply, e₁₀_mul_e₀₁]

/-- The image class is nonzero and different from the source class. -/
theorem sandwich_mk_e₀₁_e₁₀_ne :
    sandwich (TensorProduct.Balanced.mk ℚ R R R e₀₁ e₁₀) ≠ 0 ∧
      sandwich (TensorProduct.Balanced.mk ℚ R R R e₀₁ e₁₀) ≠
        TensorProduct.Balanced.mk ℚ R R R e₀₁ e₁₀ := by
  rw [sandwich_mk_e₀₁_e₁₀]
  constructor
  · intro h
    have h₁ := mulLift_mk e₁₁ e₁₁
    rw [h, map_zero, e₁₁_mul_e₁₁] at h₁
    exact e₁₁_ne_zero h₁.symm
  · intro h
    have h₁ := congrArg mulLift h
    rw [mulLift_mk, mulLift_mk, e₁₁_mul_e₁₁, e₀₁_mul_e₁₀] at h₁
    exact e₁₁_ne_e₀₀ h₁

/-- By `hom_ext`, the induced map intertwines the descent of multiplication with the
two-sided multiplication `x ↦ e₁₀ * x * e₀₁`. The pure-class check uses associativity. -/
theorem mulLift_comp_sandwich :
    mulLift ∘ₗ sandwich = (LinearMap.mulLeft ℚ e₁₀ ∘ₗ LinearMap.mulRight ℚ e₀₁) ∘ₗ mulLift := by
  apply TensorProduct.Balanced.hom_ext
  intro m n
  simp only [LinearMap.comp_apply, sandwich, TensorProduct.Balanced.map_mk, mulLift_mk,
    LinearMap.mulLeft_apply, LinearMap.mulRight_apply, mul_assoc]

/-! ### Free-action cancellation -/

/-- `cancelEquiv` moves the regular factor into the right action. -/
theorem cancelEquiv_value :
    TensorProduct.Balanced.cancelEquiv ℚ R R ℚ
        (TensorProduct.Balanced.mk ℚ R R (R ⊗[ℚ] ℚ) e₀₀ (e₀₁ ⊗ₜ[ℚ] (1 : ℚ))) =
      e₀₁ ⊗ₜ[ℚ] (1 : ℚ) := by
  rw [TensorProduct.Balanced.cancelEquiv_mk_tmul, op_smul_eq_mul, e₀₀_mul_e₀₁]

theorem rid_e₀₁ : TensorProduct.rid ℚ R (e₀₁ ⊗ₜ[ℚ] (1 : ℚ)) = e₀₁ := by
  rw [TensorProduct.rid_tmul, one_smul]

/-- The cancelled value is nonzero. -/
theorem cancelEquiv_value_ne_zero : e₀₁ ⊗ₜ[ℚ] (1 : ℚ) ≠ (0 : R ⊗[ℚ] ℚ) := by
  intro h
  have h₁ := rid_e₀₁
  rw [h, map_zero] at h₁
  exact e₀₁_ne_zero h₁.symm

/-- Negative guard: the regular factor is not simply dropped. -/
theorem cancelEquiv_ne_drop :
    TensorProduct.Balanced.cancelEquiv ℚ R R ℚ
        (TensorProduct.Balanced.mk ℚ R R (R ⊗[ℚ] ℚ) e₀₀ (e₀₁ ⊗ₜ[ℚ] (1 : ℚ))) ≠
      e₀₀ ⊗ₜ[ℚ] (1 : ℚ) := by
  rw [cancelEquiv_value]
  intro h
  have h₁ := congrArg (TensorProduct.rid ℚ R) h
  rw [rid_e₀₁, TensorProduct.rid_tmul, one_smul] at h₁
  exact e₀₁_ne_e₀₀ h₁

/-- The round trip through `cancel` and `insert` on a nonzero class gives a quotient identity
whose two pure representatives differ. -/
theorem insert_cancel_identity :
    TensorProduct.Balanced.mk ℚ R R (R ⊗[ℚ] ℚ) e₀₀ (e₀₁ ⊗ₜ[ℚ] (1 : ℚ)) =
      TensorProduct.Balanced.mk ℚ R R (R ⊗[ℚ] ℚ) e₀₁ ((1 : R) ⊗ₜ[ℚ] (1 : ℚ)) := by
  have h := LinearMap.congr_fun (TensorProduct.Balanced.insert_cancel ℚ R R ℚ)
    (TensorProduct.Balanced.mk ℚ R R (R ⊗[ℚ] ℚ) e₀₀ (e₀₁ ⊗ₜ[ℚ] (1 : ℚ)))
  rw [LinearMap.comp_apply, LinearMap.id_apply, TensorProduct.Balanced.cancel_mk_tmul,
    op_smul_eq_mul, e₀₀_mul_e₀₁, TensorProduct.Balanced.insert_tmul] at h
  exact h.symm

/-- The two representatives in `insert_cancel_identity` differ before the quotient. -/
theorem insert_cancel_representatives_ne :
    (e₀₀ ⊗ₜ[ℚ] (e₀₁ ⊗ₜ[ℚ] (1 : ℚ)) : R ⊗[ℚ] (R ⊗[ℚ] ℚ)) ≠
      e₀₁ ⊗ₜ[ℚ] ((1 : R) ⊗ₜ[ℚ] (1 : ℚ)) := by
  intro h
  have h₁ := congrArg
    (entryProbe 0 1 1 1 ∘ₗ TensorProduct.map LinearMap.id (TensorProduct.rid ℚ R).toLinearMap) h
  simp [entryProbe_tmul, e₀₀, e₀₁] at h₁

/-- The other round trip, on a nonzero element. -/
theorem cancel_insert_value :
    TensorProduct.Balanced.cancel ℚ R R ℚ
        (TensorProduct.Balanced.insert ℚ R R ℚ (e₁₀ ⊗ₜ[ℚ] (3 : ℚ))) =
      e₁₀ ⊗ₜ[ℚ] (3 : ℚ) := by
  rw [TensorProduct.Balanced.insert_tmul, TensorProduct.Balanced.cancel_mk_tmul, op_one,
    one_smul]

theorem cancel_insert_value_ne_zero : e₁₀ ⊗ₜ[ℚ] (3 : ℚ) ≠ (0 : R ⊗[ℚ] ℚ) := by
  intro h
  have h₁ := congrArg (fun x => TensorProduct.rid ℚ R x 1 0) h
  simp [e₁₀] at h₁

end MathlibExtTest.Algebra.Homology.BalancedTensorFocusedClients
