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

public import Mathlib.Analysis.Normed.Module.PiTensorProduct.ProjectiveSeminorm
public import Mathlib.LinearAlgebra.TensorPower.Basic
public import Mathlib.LinearAlgebra.Multilinear.Curry

/-!
# Projective seminorm bound for tensor-power concatenation

Let 𝕜 be a nontrivially normed field and V a seminormed 𝕜-vector space.
The graded concatenation of x in tensor degree m and y in degree n has
projective seminorm at most ‖x‖ · ‖y‖ in degree m+n. This includes zero
degrees and seminorms that do not separate vectors.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped TensorProduct BigOperators
namespace TensorPower
universe uK uV
variable {𝕜 : Type uK} [NontriviallyNormedField 𝕜]
variable {V : Type uV} [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- Let 𝕜 be a nontrivially normed field and V a seminormed 𝕜-vector space.
For m,n ∈ ℕ, x ∈ TensorPower 𝕜 m V and y ∈ TensorPower 𝕜 n V,
their graded concatenation satisfies ‖x · y‖ ≤ ‖x‖ · ‖y‖ for the
projective seminorms, including m = 0 or n = 0. -/
theorem norm_gMul_le {m n : ℕ} (x : TensorPower 𝕜 m V) (y : TensorPower 𝕜 n V) :
    ‖@GradedMonoid.GMul.mul ℕ (fun k => TensorPower 𝕜 k V) _ _ m n x y‖ ≤ ‖x‖ * ‖y‖ := by
  let f : MultilinearMap (RingHom.id 𝕜) (fun _ : Fin m => V)
      (MultilinearMap (RingHom.id 𝕜) (fun _ : Fin n => V) (TensorPower 𝕜 (m + n) V)) :=
    MultilinearMap.currySum
      ((PiTensorProduct.tprod 𝕜 (s := fun _ : Fin (m + n) => V)).domDomCongr finSumFinEquiv.symm)
  let GM : TensorPower 𝕜 m V →ₗ[𝕜] TensorPower 𝕜 n V →ₗ[𝕜] TensorPower 𝕜 (m + n) V :=
    (TensorProduct.mk 𝕜 _ _).compr₂
      (TensorPower.mulEquiv (R := 𝕜) (M := V) (n := m) (m := n)).toLinearMap
  have hf (a : Fin m → V) (b : Fin n → V) :
      f a b = GM (PiTensorProduct.tprod 𝕜 a) (PiTensorProduct.tprod 𝕜 b) := by
    change f a b = @GradedMonoid.GMul.mul ℕ (fun k => TensorPower 𝕜 k V) _ _ m n
      (PiTensorProduct.tprod 𝕜 a) (PiTensorProduct.tprod 𝕜 b)
    rw [TensorPower.tprod_mul_tprod]
    change PiTensorProduct.tprod 𝕜 (fun i => Sum.elim a b (finSumFinEquiv.symm i)) =
      PiTensorProduct.tprod 𝕜 (Fin.append a b)
    congr 1
    dsimp only [Fin.append, finSumFinEquiv, Equiv.coe_fn_symm_mk]
    apply funext
    apply Fin.addCases <;> simp
  have hfBound (a : Fin m → V) (b : Fin n → V) :
      ‖f a b‖ ≤ (1 * ∏ i, ‖a i‖) * ∏ j, ‖b j‖ := by
    change ‖PiTensorProduct.tprod 𝕜 (fun i => Sum.elim a b (finSumFinEquiv.symm i))‖ ≤ _
    have hprod :
        (∏ i : Fin (m + n), ‖Sum.elim a b (finSumFinEquiv.symm i)‖) =
          (∏ i : Fin m, ‖a i‖) * ∏ j : Fin n, ‖b j‖ := by
      exact ((finSumFinEquiv.symm).prod_comp
        (fun i : Fin m ⊕ Fin n => ‖Sum.elim a b i‖)).trans (by
          simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr])
    simpa only [_root_.one_mul, hprod] using
      PiTensorProduct.projectiveSeminorm_tprod_le (𝕜 := 𝕜)
        (fun i : Fin (m + n) => Sum.elim a b (finSumFinEquiv.symm i))
  let fc := MultilinearMap.mkContinuousMultilinear f 1 hfBound
  let L := (PiTensorProduct.liftIsometry 𝕜 (fun _ : Fin n => V)
    (TensorPower 𝕜 (m + n) V)).toLinearIsometry
  let outer := L.toContinuousLinearMap.compContinuousMultilinearMap fc
  let B := PiTensorProduct.liftIsometry 𝕜 (fun _ : Fin m => V)
    (TensorPower 𝕜 n V →L[𝕜] TensorPower 𝕜 (m + n) V) outer
  have hnorm : ‖B‖ ≤ 1 := by
    have hfc : ‖fc‖ ≤ 1 :=
      MultilinearMap.mkContinuousMultilinear_norm_le f zero_le_one hfBound
    have ho : ‖outer‖ = ‖fc‖ := L.norm_compContinuousMultilinearMap fc
    have hb : ‖B‖ = ‖outer‖ :=
      (PiTensorProduct.liftIsometry 𝕜 (fun _ : Fin m => V)
        (TensorPower 𝕜 n V →L[𝕜] TensorPower 𝕜 (m + n) V)).norm_map outer
    exact hb.trans_le (ho.trans_le hfc)
  have hpure (a : Fin m → V) (b : Fin n → V) :
      B (PiTensorProduct.tprod 𝕜 a) (PiTensorProduct.tprod 𝕜 b) = f a b := by
    dsimp only [B]
    rw [PiTensorProduct.liftIsometry_apply_apply, PiTensorProduct.lift.tprod]
    change outer a (PiTensorProduct.tprod 𝕜 b) = f a b
    have houter : outer a = PiTensorProduct.liftIsometry 𝕜 (fun _ : Fin n => V)
        (TensorPower 𝕜 (m + n) V) (fc a) := by
      simp only [outer, L, ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
        LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry]
    rw [houter]
    rw [PiTensorProduct.liftIsometry_apply_apply, PiTensorProduct.lift.tprod]
    rfl
  have hvalue : B x y = GM x y := by
    induction x using PiTensorProduct.induction_on with
    | smul_tprod c a =>
      induction y using PiTensorProduct.induction_on with
      | smul_tprod d b =>
        simp only [map_smul, _root_.smul_apply, LinearMap.smul_apply]
        rw [hpure]
        simpa only [_root_.smul_smul, _root_.mul_comm] using
          congrArg (fun z => c • (d • z)) (hf a b)
      | add y₁ y₂ h₁ h₂ =>
        simpa only [map_add] using congrArg₂ (fun a b => a + b) h₁ h₂
    | add x₁ x₂ h₁ h₂ =>
      simpa only [map_add, _root_.add_apply, LinearMap.add_apply] using
        congrArg₂ (fun a b => a + b) h₁ h₂
  change ‖GM x y‖ ≤ ‖x‖ * ‖y‖
  rw [← hvalue]
  calc
    ‖B x y‖ ≤ ‖B x‖ * ‖y‖ := (B x).le_opNorm y
    _ ≤ (‖B‖ * ‖x‖) * ‖y‖ :=
      mul_le_mul_of_nonneg_right (B.le_opNorm x) (norm_nonneg y)
    _ ≤ (1 * ‖x‖) * ‖y‖ := by gcongr
    _ = _ := by rw [_root_.one_mul]

end TensorPower
