/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Normed.Algebra.OrderedExponential
import Mathlib.Analysis.Matrix.Normed

/-! Tests for time-ordered products: every public statement restated. -/

namespace MathlibExtTest.Analysis.Normed.Algebra.OrderedExponential

open _root_.NormedSpace


open Filter Topology Set MeasureTheory


section BanachAlgebra

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]

/-- **Well-posedness.** A bounded piecewise continuous `Y` has a time-ordered exponential on
`[0, t]`, unique on `[0, t]`. -/
example {Y : ℝ → 𝔸} {t : ℝ} (ht : 0 ≤ t)
    (hY : PiecewiseContinuousOn Y t) (hb : ∃ C, ∀ s ∈ Icc 0 t, ‖Y s‖ ≤ C) :
    ∃ U, IsOrderedExp Y U t ∧ ∀ V, IsOrderedExp Y V t → EqOn V U (Icc 0 t) := by
  apply _root_.NormedSpace.existsUnique_isOrderedExp <;> assumption

/-- **Time-ordered product limit.** If `Y M → Y₀` uniformly on `[0, t]`, with `Y₀` bounded
and piecewise continuous, and `U` is the time-ordered exponential of `Y₀` on `[0, t]`, then
`∏_{g < t M} (1 + M⁻¹ Y_M(g / M)) → U t`. -/
example {Y : ℕ → ℝ → 𝔸} {Y₀ U : ℝ → 𝔸} {t : ℝ} (ht : 0 ≤ t)
    (hconv : TendstoUniformlyOn Y Y₀ atTop (Icc 0 t)) (hY₀ : PiecewiseContinuousOn Y₀ t)
    (hb : ∃ C, ∀ s ∈ Icc 0 t, ‖Y₀ s‖ ≤ C) (hU : IsOrderedExp Y₀ U t) :
    Tendsto (fun M : ℕ => gridProd (Y M) t M) atTop (𝓝 (U t)) := by
  apply _root_.NormedSpace.tendsto_gridProd <;> assumption

/-- **Constant `Y`:** `s ↦ exp (s A)` is the time-ordered exponential of `Y ≡ A`. -/
example (A : 𝔸) (t : ℝ) :
    IsOrderedExp (fun _ => A) (fun s => exp (s • A)) t := by
  apply _root_.NormedSpace.isOrderedExp_const <;> assumption

/-- **Two-piece `Y`:** for `Y = A` on `[0, t₁)` and `Y = B` from `t₁` on, the time-ordered
exponential is `exp (s A)` up to `t₁` and `exp (t₁ A) * exp ((s - t₁) B)` after. -/
example (A B : 𝔸) {t₁ t : ℝ} (h₁ : 0 ≤ t₁) (h : t₁ ≤ t) :
    IsOrderedExp (fun s => if s < t₁ then A else B)
      (fun s => if s ≤ t₁ then exp (s • A) else exp (t₁ • A) * exp ((s - t₁) • B)) t := by
  apply _root_.NormedSpace.isOrderedExp_piecewise <;> assumption

/-- **Acceptance, constant `Y`:** `∏_{g < t M} (1 + M⁻¹ A) → exp (t A)`. -/
example (A : 𝔸) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun M : ℕ => gridProd (fun _ => A) t M) atTop (𝓝 (exp (t • A))) := by
  apply _root_.NormedSpace.tendsto_gridProd_const <;> assumption

/-- **Acceptance, two-piece `Y`:** the grid products converge to
`exp (t₁ A) * exp ((t - t₁) B)`. -/
example (A B : 𝔸) {t₁ t : ℝ} (h₁ : 0 ≤ t₁) (h : t₁ ≤ t) :
    Tendsto (fun M : ℕ => gridProd (fun s => if s < t₁ then A else B) t M) atTop
      (𝓝 (exp (t₁ • A) * exp ((t - t₁) • B))) := by
  apply _root_.NormedSpace.tendsto_gridProd_piecewise <;> assumption

end BanachAlgebra

section Matrix

open scoped Matrix.Norms.Operator

/-- **Finite matrices with the operator norm**: the generic `tendsto_gridProd` specialized
at `Matrix n n ℝ`. -/
example {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {Y : ℕ → ℝ → Matrix n n ℝ} {Y₀ U : ℝ → Matrix n n ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hconv : TendstoUniformlyOn Y Y₀ atTop (Icc 0 t)) (hY₀ : PiecewiseContinuousOn Y₀ t)
    (hb : ∃ C, ∀ s ∈ Icc 0 t, ‖Y₀ s‖ ≤ C) (hU : IsOrderedExp Y₀ U t) :
    Tendsto (fun M : ℕ => gridProd (Y M) t M) atTop (𝓝 (U t)) :=
  tendsto_gridProd ht hconv hY₀ hb hU

/-- At time `0` the grid product is empty, hence `1`, for every `M`. -/
example (Y : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (M : ℕ) : gridProd Y 0 M = 1 := by
  simp [gridProd]

/-- Factor order matters: for the two-piece coefficient with noncommuting pieces
`A = !![0, 1; 0, 0]`, `B = !![0, 0; 1, 0]`, breakpoint `t₁ = 1`, horizon `t = 2`, and
`M = 1`, the grid product is `(1 + A) * (1 + B)`, not `(1 + B) * (1 + A)`. -/
example :
    gridProd (fun s => if s < 1 then (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ)
        else !![0, 0; 1, 0]) 2 1 =
      (1 + !![0, 1; 0, 0]) * (1 + !![0, 0; 1, 0]) ∧
    gridProd (fun s => if s < 1 then (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ)
        else !![0, 0; 1, 0]) 2 1 ≠
      (1 + !![0, 0; 1, 0]) * (1 + !![0, 1; 0, 0]) := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [gridProd, List.range_succ, List.map_append, List.prod_append, Matrix.mul_apply,
        Fin.sum_univ_two] <;>
      norm_num
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    simp [gridProd, List.range_succ, List.map_append, List.prod_append, Matrix.mul_apply,
      Fin.sum_univ_two] at h00

/-- A non-grid-aligned horizon: constant `A = !![2, 0; 0, 0]`, `t = 5 / 4`, `M = 2` gives
`⌈5 / 2⌉₊ = 3` factors of `1 + A / 2` (the last factor overshoots `t`), i.e.
`!![8, 0; 0, 1]`. -/
example :
    gridProd (fun _ => (!![2, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ)) (5 / 4) 2 =
      !![8, 0; 0, 1] := by
  have hc : ⌈(5 / 4 : ℝ) * ((2 : ℕ) : ℝ)⌉₊ = 3 := by
    have h1 : ⌈(5 / 4 : ℝ) * ((2 : ℕ) : ℝ)⌉₊ ≤ 3 := Nat.ceil_le.2 (by norm_num)
    have h2 : 2 < ⌈(5 / 4 : ℝ) * ((2 : ℕ) : ℝ)⌉₊ := Nat.lt_ceil.2 (by norm_num)
    omega
  unfold gridProd
  rw [hc]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [List.prod_cons, List.prod_nil, Matrix.mul_apply, Fin.sum_univ_two] <;>
    norm_num [pow_succ, Matrix.mul_apply, Fin.sum_univ_two]

end Matrix

end MathlibExtTest.Analysis.Normed.Algebra.OrderedExponential
