/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_CerednikDrinfeld_SpecialModule_exists_forall_apply_eq_mul_`
`dotProduct_mulVec_of_forall_apply_mulVec_eq_apply_inv_mul_adjugate_mul_mulVec.lean`
and
`P2M/Sol/S_CerednikDrinfeld_SpecialModule_exists_forall_apply_eq_mul_`
`dotProduct_mulVec_of_forall_apply_mulVec_eq_apply_inv_mul_adjugate_mul_mulVec.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

open Matrix

/-- A bilinear form on `Fin 2 → k` that is invariant under
adjugate-conjugation by an invertible matrix `μ` is a scalar
multiple of the form `(v, w) ↦ dotProduct v ((J * μ).mulVec w)`, where
`J = !![0, 1; -1, 0]`. -/
theorem exists_forall_apply_eq_mul_dotProduct_mulVec_of_forall_apply_mulVec_eq
    {k : Type*} [Field k] (μ : Matrix (Fin 2) (Fin 2) k)
    (hdet : μ.det ≠ 0)
    (b : (Fin 2 → k) →ₗ[k] (Fin 2 → k) →ₗ[k] k)
    (hb : ∀ (x : Matrix (Fin 2) (Fin 2) k) (v w : Fin 2 → k),
      b (x.mulVec v) w = b v ((μ⁻¹ * x.adjugate * μ).mulVec w)) :
    ∃ c : k, ∀ v w : Fin 2 → k,
      b v w = c * dotProduct v ((!![0, 1; -1, 0] * μ).mulVec w) := by
  classical
  have hμu : IsUnit μ.det := isUnit_iff_ne_zero.mpr hdet
  have hμinv : ∀ z : Fin 2 → k, μ.mulVec (μ⁻¹.mulVec z) = z := fun z => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hμu, Matrix.one_mulVec]
  have key : ∀ (A : Matrix (Fin 2) (Fin 2) k) (v w : Fin 2 → k),
      b (A.mulVec v) w =
        b v (μ⁻¹.mulVec (A.adjugate.mulVec (μ.mulVec w))) := by
    intro A v w
    rw [hb, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have hmv : ∀ (A : Matrix (Fin 2) (Fin 2) k) (z : Fin 2 → k) (i : Fin 2),
      A.mulVec z i = A i 0 * z 0 + A i 1 * z 1 := by
    intro A z i; simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hv0 : ∀ c : k, (![0, c] : Fin 2 → k) = c • ![0, 1] := fun c => by
    ext i; fin_cases i <;> simp
  have hv1 : ∀ c : k, (![c, 0] : Fin 2 → k) = c • ![1, 0] := fun c => by
    ext i; fin_cases i <;> simp
  have hA00v : ∀ v : Fin 2 → k,
      (!![(1 : k), 0; 0, 0]).mulVec v = ![v 0, 0] := fun v => by
    ext i; fin_cases i <;> simp [hmv]
  have hA11v : ∀ v : Fin 2 → k,
      (!![(0 : k), 0; 0, 1]).mulVec v = ![0, v 1] := fun v => by
    ext i; fin_cases i <;> simp [hmv]
  have hA01v : ∀ v : Fin 2 → k,
      (!![(0 : k), 1; 0, 0]).mulVec v = ![v 1, 0] := fun v => by
    ext i; fin_cases i <;> simp [hmv]
  have hA01nv : ∀ v : Fin 2 → k,
      (!![(0 : k), -1; 0, 0]).mulVec v = ![-v 1, 0] := fun v => by
    ext i; fin_cases i <;> simp [hmv]
  have hadj00 : (!![(1 : k), 0; 0, 0]).adjugate = !![(0 : k), 0; 0, 1] := by
    rw [Matrix.adjugate_fin_two_of]; norm_num
  have hadj11 : (!![(0 : k), 0; 0, 1]).adjugate = !![(1 : k), 0; 0, 0] := by
    rw [Matrix.adjugate_fin_two_of]; norm_num
  have hadj01 : (!![(0 : k), 1; 0, 0]).adjugate = !![(0 : k), -1; 0, 0] := by
    rw [Matrix.adjugate_fin_two_of]; norm_num
  set u₀ : Fin 2 → k := μ⁻¹.mulVec ![1, 0] with hu₀
  set u₁ : Fin 2 → k := μ⁻¹.mulVec ![0, 1] with hu₁
  set α : k := b ![1, 0] u₁ with hα
  set β : k := b ![0, 1] u₀ with hβ
  have hE3 : ∀ w, b ![1, 0] w = (μ.mulVec w) 1 * α := by
    intro w
    have h := key !![(1 : k), 0; 0, 0] ![1, 0] w
    rw [hadj00, hA00v, hA11v, hv0 ((μ.mulVec w) 1), Matrix.mulVec_smul,
      map_smul, smul_eq_mul] at h
    simp only [Matrix.cons_val_zero] at h
    exact h
  have hE4 : ∀ w, b ![0, 1] w = (μ.mulVec w) 0 * β := by
    intro w
    have h := key !![(0 : k), 0; 0, 1] ![0, 1] w
    rw [hadj11, hA11v, hA00v, hv1 ((μ.mulVec w) 0), Matrix.mulVec_smul,
      map_smul, smul_eq_mul] at h
    simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero] at h
    exact h
  have hE5 : ∀ w, b ![1, 0] w = -(μ.mulVec w) 1 * β := by
    intro w
    have h := key !![(0 : k), 1; 0, 0] ![0, 1] w
    rw [hadj01, hA01v, hA01nv, hv1 (-(μ.mulVec w) 1), Matrix.mulVec_smul,
      map_smul, smul_eq_mul] at h
    simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero] at h
    exact h
  have hαβ : α = -β := by
    have h3 := hE3 (μ⁻¹.mulVec ![0, 1])
    have h5 := hE5 (μ⁻¹.mulVec ![0, 1])
    rw [hμinv] at h3 h5
    simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero,
      one_mul, neg_mul] at h3 h5
    rw [← h3, h5]
  have hbv : ∀ x y : Fin 2 → k,
      b x y = x 0 * b ![1, 0] y + x 1 * b ![0, 1] y := by
    intro x y
    have hx : x = x 0 • ![1, 0] + x 1 • ![0, 1] := by
      ext i; fin_cases i <;> simp
    conv_lhs => rw [hx]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul]
  have hJ : ∀ w : Fin 2 → k,
      (!![(0 : k), 1; -1, 0] * μ).mulVec w =
        ![(μ.mulVec w) 1, -(μ.mulVec w) 0] := by
    intro w
    rw [← Matrix.mulVec_mulVec]
    ext i; fin_cases i <;> simp [hmv]
  refine ⟨α, fun v w => ?_⟩
  rw [hbv v w, hE3, hE4, hJ]
  simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons]
  rw [hαβ]
  ring
