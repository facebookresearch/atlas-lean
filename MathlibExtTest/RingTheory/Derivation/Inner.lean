/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
The exact-source consumer statement and scalar-extension comparison below
are adapted from the following files:
Theorems/Thm_Algebra_exists_forall_add_sub_eq_zero_of_map_mul_of_separabilityElement_tensor.lean
P2M/Sol/S_Algebra_exists_forall_add_sub_eq_zero_of_map_mul_of_separabilityElement_tensor.lean
at FLT 6e837e75355538c7f80bab5b956861e86c4eacc2.
Copyright 2026 Anthropic, PBC. Apache License, Version 2.0.
https://www.apache.org/licenses/LICENSE-2.0
No individual authors are supplied for that file upstream.
The matrix and block applications and boundaries are original here.
-/
import MathlibExt.RingTheory.Derivation.Inner
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Algebra.Azumaya.Defs

open scoped TensorProduct

universe u v w

-- The two canonical integer-module presentations on a nested tensor are
-- definitionally equal; let elaboration unfold them when inferring its ring.
set_option backward.isDefEq.respectTransparency false

namespace InnerDerivationTest

-- The exact source-shaped consumer keeps all hypotheses and universes.
theorem exactSource
    (k : Type u) [CommRing k] (Λ : Type v) [Ring Λ]
    (e : (k ⊗[ℤ] Λ) ⊗[k] (k ⊗[ℤ] Λ))
    (he₁ : LinearMap.mul' k (k ⊗[ℤ] Λ) e = 1)
    (he₂ : ∀ x : k ⊗[ℤ] Λ,
      TensorProduct.map (LinearMap.mulLeft k x) LinearMap.id e =
      TensorProduct.map LinearMap.id (LinearMap.mulRight k x) e)
    (M : Type w) [AddCommGroup M] [Module k M]
    (θ : Λ →+* Module.End k M) (ρ : Λᵐᵒᵖ →+* Module.End k M)
    (hθρ : ∀ (x : Λ) (y : Λᵐᵒᵖ),
      (θ x).comp (ρ y) = (ρ y).comp (θ x))
    (o : Λ →+ M)
    (ho : ∀ x y : Λ, o (x * y) = θ x (o y) + ρ (MulOpposite.op y) (o x)) :
    ∃ ξ : M, ∀ x : Λ, o x + θ x ξ - ρ (MulOpposite.op x) ξ = 0 :=
  Algebra.exists_inner_of_separabilityElement k Λ e he₁ he₂ M θ ρ hθρ o ho

abbrev Mat := Matrix (Fin 2) (Fin 2) ℤ

private def E (i j : Fin 2) : Mat := Matrix.single i j 1

private theorem mul_E (x : Mat) (i j : Fin 2) :
    x * E i j = x 0 i • E 0 j + x 1 i • E 1 j := by
  ext a b
  fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;>
    simp [E, Matrix.mul_apply, Matrix.single]

private theorem E_mul (x : Mat) (i j : Fin 2) :
    E i j * x = x j 0 • E i 0 + x j 1 • E i 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;>
    simp [E, Matrix.mul_apply, Matrix.single]

private def C : Mat ⊗[ℤ] Mat :=
  E 0 0 ⊗ₜ[ℤ] E 0 0 + E 1 0 ⊗ₜ[ℤ] E 0 1

private theorem C_balance (x : Mat) :
    TensorProduct.map (LinearMap.mulLeft ℤ x) LinearMap.id C =
      TensorProduct.map LinearMap.id (LinearMap.mulRight ℤ x) C := by
  simp only [C, map_add, TensorProduct.map_tmul, LinearMap.mulLeft_apply,
    LinearMap.mulRight_apply, LinearMap.id_apply, mul_E, E_mul,
    TensorProduct.add_tmul, TensorProduct.tmul_add,
    TensorProduct.smul_tmul, TensorProduct.tmul_smul]
  abel

private theorem C_mul : LinearMap.mul' ℤ Mat C = 1 := by
  simp only [C, map_add, LinearMap.mul'_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [E, Matrix.mul_apply, Matrix.single]

private abbrev BaseMat := ℤ ⊗[ℤ] Mat

private noncomputable def baseEquiv : BaseMat ≃ₐ[ℤ] Mat :=
  Algebra.TensorProduct.lid ℤ Mat

private noncomputable def tensorEquiv :
    (Mat ⊗[ℤ] Mat) ≃ₐ[ℤ] (BaseMat ⊗[ℤ] BaseMat) :=
  Algebra.TensorProduct.congr baseEquiv.symm baseEquiv.symm

private theorem tensorEquiv_tmul (a b : Mat) :
    tensorEquiv (a ⊗ₜ[ℤ] b) =
      baseEquiv.symm a ⊗ₜ[ℤ] baseEquiv.symm b := rfl

private theorem tensor_left (x : BaseMat) (z : Mat ⊗[ℤ] Mat) :
    TensorProduct.map (LinearMap.mulLeft ℤ x) LinearMap.id (tensorEquiv z) =
      tensorEquiv (TensorProduct.map
        (LinearMap.mulLeft ℤ (baseEquiv x)) LinearMap.id z) := by
  induction z using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a b =>
    simp only [tensorEquiv_tmul, TensorProduct.map_tmul,
      LinearMap.mulLeft_apply, LinearMap.id_apply]
    rw [map_mul, baseEquiv.symm_apply_apply]

private theorem tensor_right (x : BaseMat) (z : Mat ⊗[ℤ] Mat) :
    TensorProduct.map LinearMap.id (LinearMap.mulRight ℤ x) (tensorEquiv z) =
      tensorEquiv (TensorProduct.map LinearMap.id
        (LinearMap.mulRight ℤ (baseEquiv x)) z) := by
  induction z using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a b =>
    simp only [tensorEquiv_tmul, TensorProduct.map_tmul,
      LinearMap.mulRight_apply, LinearMap.id_apply]
    rw [map_mul, baseEquiv.symm_apply_apply]

private theorem tensor_mul (z : Mat ⊗[ℤ] Mat) :
    LinearMap.mul' ℤ BaseMat (tensorEquiv z) =
      baseEquiv.symm (LinearMap.mul' ℤ Mat z) := by
  induction z using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a b =>
    simp only [tensorEquiv_tmul, LinearMap.mul'_apply, map_mul]

private theorem e_mul :
    LinearMap.mul' ℤ BaseMat (tensorEquiv C) = 1 := by
  rw [tensor_mul, C_mul, map_one]

private theorem e_balance (x : BaseMat) :
    TensorProduct.map (LinearMap.mulLeft ℤ x) LinearMap.id
        (tensorEquiv C) =
      TensorProduct.map LinearMap.id (LinearMap.mulRight ℤ x)
        (tensorEquiv C) := by
  rw [tensor_left, tensor_right, C_balance]

private noncomputable def leftAction : Mat →+* Module.End ℤ Mat :=
  ((AlgHom.mulLeftRight ℤ Mat).comp Algebra.TensorProduct.includeLeft).toRingHom

private noncomputable def rightAction : Matᵐᵒᵖ →+* Module.End ℤ Mat :=
  ((AlgHom.mulLeftRight ℤ Mat).comp
    Algebra.TensorProduct.includeRight).toRingHom

private theorem left_apply (x m : Mat) : leftAction x m = x * m := by
  simp [leftAction]

private theorem right_apply (x : Matᵐᵒᵖ) (m : Mat) :
    rightAction x m = m * x.unop := by
  simp [rightAction]

private theorem actions_commute (x : Mat) (y : Matᵐᵒᵖ) :
    (leftAction x).comp (rightAction y) =
      (rightAction y).comp (leftAction x) := by
  ext m
  simp [LinearMap.comp_apply, left_apply, right_apply, mul_assoc]

/-- All additive derivations of the regular integer matrix bimodule
are inner. -/
theorem matrix_inner (o : Mat →+ Mat)
    (ho : ∀ x y, o (x * y) = x * o y + o x * y) :
    ∃ ξ : Mat, ∀ x, o x + x * ξ - ξ * x = 0 := by
  have h (x y : Mat) : o (x * y) =
      leftAction x (o y) + rightAction (MulOpposite.op y) (o x) := by
    simpa only [left_apply, right_apply, MulOpposite.unop_op] using ho x y
  simpa only [left_apply, right_apply, MulOpposite.unop_op] using
    Algebra.exists_inner_of_separabilityElement ℤ Mat (tensorEquiv C)
      e_mul e_balance Mat leftAction rightAction actions_commute o h

private def commutator : Mat →+ Mat where
  toFun x := E 0 0 * x - x * E 0 0
  map_zero' := by simp
  map_add' x y := by simp only [mul_add, add_mul]; abel

private theorem commutator_leibniz (x y : Mat) :
    commutator (x * y) = x * commutator y + commutator x * y := by
  change E 0 0 * (x * y) - (x * y) * E 0 0 =
    x * (E 0 0 * y - y * E 0 0) + (E 0 0 * x - x * E 0 0) * y
  simp only [mul_sub, sub_mul, mul_assoc]
  abel

private theorem E_product (i j k l : Fin 2) :
    E i j * E k l = if j = k then E i l else 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;>
    fin_cases k <;> fin_cases l <;> simp [E, Matrix.mul_apply, Matrix.single]

theorem noncommutation : E 0 0 * E 0 1 = E 0 1 ∧ E 0 1 * E 0 0 = 0 := by
  simp [E_product]

theorem right_reverses (x y m : Mat) :
    rightAction (MulOpposite.op (x * y)) m =
      rightAction (MulOpposite.op y) (rightAction (MulOpposite.op x) m) := by
  simp only [right_apply, MulOpposite.unop_op, mul_assoc]

private theorem C_square : C * C = E 0 0 ⊗ₜ[ℤ] E 0 0 := by
  simp [C, add_mul, mul_add, Algebra.TensorProduct.tmul_mul_tmul, E_product]

private def entry (i j : Fin 2) : Mat →ₗ[ℤ] ℤ where
  toFun x := x i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem ordinary_tensor_not_idempotent : C * C ≠ C := by
  intro h
  let F := (LinearMap.mul' ℤ ℤ).comp
    (TensorProduct.map (entry 1 0) (entry 0 1))
  have q := congrArg F h
  rw [C_square] at q
  simp [F, C, entry, E, Matrix.single] at q

theorem commutator_nonzero : commutator ≠ 0 := by
  intro h
  have q := congrArg (fun f : Mat →+ Mat => f (E 0 1) 0 1) h
  simp [commutator, E, Matrix.single, Matrix.mul_apply] at q

theorem commutator_inner :
    ∃ ξ : Mat, ∀ x, commutator x + x * ξ - ξ * x = 0 :=
  matrix_inner commutator commutator_leibniz

theorem distinct_witnesses :
    (∀ x : Mat, commutator x + x * E 0 0 - E 0 0 * x = 0) ∧
    (∀ x : Mat, commutator x + x * (-E 1 1) - (-E 1 1) * x = 0) ∧
    E 0 0 ≠ -E 1 1 := by
  have shift : -E 1 1 = E 0 0 - 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [E, Matrix.single]
  refine ⟨?_, ?_, ?_⟩
  · intro x
    change (E 0 0 * x - x * E 0 0) + x * E 0 0 - E 0 0 * x = 0
    abel
  · intro x
    rw [shift]
    change (E 0 0 * x - x * E 0 0) + x * (E 0 0 - 1) -
      (E 0 0 - 1) * x = 0
    simp only [mul_sub, sub_mul, mul_one, one_mul]
    abel
  · intro h
    have q := congrArg (fun x : Mat => x 0 0) h
    simp [E, Matrix.single] at q

/-- The swap-conjugation automorphism, on the canonical matrix carrier. -/
def σ : Mat ≃+* Mat := Matrix.reindexRingEquiv ℤ (Equiv.swap 0 1)

theorem swap_conjugation (x : Mat) :
    σ x = (E 0 1 + E 1 0) * x * (E 0 1 + E 1 0) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [σ, Matrix.reindex_apply, E, Matrix.single, Matrix.mul_apply]

private noncomputable def twistedRight : Matᵐᵒᵖ →+* Module.End ℤ Mat :=
  rightAction.comp σ.toRingHom.op

private theorem twisted_apply (x : Matᵐᵒᵖ) (m : Mat) :
    twistedRight x m = m * σ x.unop := by
  change rightAction (MulOpposite.op (σ x.unop)) m = _
  rw [right_apply, MulOpposite.unop_op]

private theorem twisted_commute (x : Mat) (y : Matᵐᵒᵖ) :
    (leftAction x).comp (twistedRight y) =
      (twistedRight y).comp (leftAction x) := by
  ext m
  simp [LinearMap.comp_apply, left_apply, twisted_apply, mul_assoc]

/-- The same separability tensor splits every swap-twisted additive cocycle. -/
theorem twisted_inner (δ : Mat →+ Mat)
    (hδ : ∀ x y, δ (x * y) = x * δ y + δ x * σ y) :
    ∃ ξ : Mat, ∀ x, δ x + x * ξ - ξ * σ x = 0 := by
  have h (x y : Mat) : δ (x * y) =
      leftAction x (δ y) + twistedRight (MulOpposite.op y) (δ x) := by
    simpa only [left_apply, twisted_apply, MulOpposite.unop_op] using hδ x y
  simpa only [left_apply, twisted_apply, MulOpposite.unop_op] using
    Algebra.exists_inner_of_separabilityElement ℤ Mat (tensorEquiv C)
      e_mul e_balance Mat leftAction twistedRight twisted_commute δ h

abbrev Block := Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ

/-- Upper triangular block representations of an additive twisted cocycle. -/
def blockRep (δ : Mat →+ Mat)
    (hδ : ∀ x y, δ (x * y) = x * δ y + δ x * σ y) : Mat →+* Block where
  toFun x := Matrix.fromBlocks x (δ x) 0 (σ x)
  map_zero' := by simp
  map_one' := by
    have h := hδ 1 1
    simp only [one_mul, map_one, mul_one] at h
    have hz : δ 1 = 0 := add_eq_left.mp h.symm
    simp [hz]
  map_add' x y := by simp [Matrix.fromBlocks_add]
  map_mul' x y := by simp [Matrix.fromBlocks_multiply, hδ]

/-- The change of splitting and its inverse are actual block matrices. -/
def U (ξ : Mat) : Block := Matrix.fromBlocks 1 ξ 0 1

/-- Every twisted extension is conjugate to its diagonal representation. -/
theorem block_extension_splits (δ : Mat →+ Mat)
    (hδ : ∀ x y, δ (x * y) = x * δ y + δ x * σ y) :
    ∃ ξ : Mat, U ξ * U (-ξ) = 1 ∧ U (-ξ) * U ξ = 1 ∧
      ∀ x, U ξ * Matrix.fromBlocks x 0 0 (σ x) * U (-ξ) = blockRep δ hδ x := by
  obtain ⟨ξ, hξ⟩ := twisted_inner δ hδ
  refine ⟨ξ, ?_, ?_, ?_⟩
  · simp [U, Matrix.fromBlocks_multiply]
  · simp [U, Matrix.fromBlocks_multiply]
  · intro x
    have h : δ x = ξ * σ x - x * ξ :=
      eq_sub_iff_add_eq.mpr (sub_eq_zero.mp (hξ x))
    change U ξ * Matrix.fromBlocks x 0 0 (σ x) * U (-ξ) =
      Matrix.fromBlocks x (δ x) 0 (σ x)
    simp [U, Matrix.fromBlocks_multiply, h, sub_eq_add_neg, add_comm]

/-- A concrete nonzero cocycle for the swap-twisted bimodule. -/
def swapCocycle : Mat →+ Mat :=
  σ.toAddEquiv.toAddMonoidHom - AddMonoidHom.id Mat

theorem swapCocycle_leibniz (x y : Mat) :
    swapCocycle (x * y) = x * swapCocycle y + swapCocycle x * σ y := by
  change σ (x * y) - x * y = x * (σ y - y) + (σ x - x) * σ y
  rw [map_mul, mul_sub, sub_mul]
  abel

theorem swapCocycle_nonzero : swapCocycle ≠ 0 := by
  intro h
  have q := congrArg (fun f : Mat →+ Mat => f (E 0 0) 0 0) h
  simp [swapCocycle, σ, Matrix.reindex_apply, E, Matrix.single] at q

theorem swap_nonidentity : σ ≠ RingEquiv.refl Mat := by
  intro h
  have q := congrArg (fun f : Mat ≃+* Mat => f (E 0 0) 0 0) h
  simp [σ, Matrix.reindex_apply, E, Matrix.single] at q

theorem nontrivial_block_extension :
    ∃ ξ : Mat, U ξ * U (-ξ) = 1 ∧ U (-ξ) * U ξ = 1 ∧
      ∀ x, U ξ * Matrix.fromBlocks x 0 0 (σ x) * U (-ξ) =
        blockRep swapCocycle swapCocycle_leibniz x :=
  block_extension_splits swapCocycle swapCocycle_leibniz

/-- The source helper is the canonical scalar-extension map, not a new API. -/
theorem source_extension_eq
    (k : Type u) [CommRing k] (Λ : Type v) [Ring Λ]
    (M : Type w) [AddCommGroup M] [Module k M] (φ : Λ →ₗ[ℤ] M) :
    TensorProduct.AlgebraTensorModule.lift
      ((LinearMap.id : k →ₗ[k] k).smulRight φ) = φ.liftBaseChange k := by
  ext c
  rfl

/-- Restriction to `1 ⊗ x` and extension are inverse on the actual maps. -/
theorem scalar_extension_characterization
    (k : Type u) [CommRing k] (Λ : Type v) [Ring Λ]
    (M : Type w) [AddCommGroup M] [Module k M]
    (f : Λ →+ M) (F : k ⊗[ℤ] Λ →ₗ[k] M) :
    F = f.toIntLinearMap.liftBaseChange k ↔
      ∀ x, F (1 ⊗ₜ[ℤ] x) = f x := by
  constructor
  · intro h x
    rw [h, LinearMap.liftBaseChange_one_tmul]
    rfl
  · intro h
    apply (LinearMap.liftBaseChangeEquiv k).symm.injective
    ext x
    simp only [LinearMap.liftBaseChangeEquiv_symm_apply,
      LinearMap.liftBaseChange_one_tmul]
    exact h x

end InnerDerivationTest
