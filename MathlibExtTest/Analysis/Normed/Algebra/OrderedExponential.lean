/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Normed.Algebra.OrderedExponential

/-! Tests for time-ordered products: every public statement restated. -/

namespace MathlibExtTest.Analysis.Normed.Algebra.OrderedExponential

open _root_.NormedSpace


open Filter Topology Set MeasureTheory


section BanachAlgebra

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]

/-- `Y` is **piecewise continuous on `[0, t]`**: continuous within `[0, t]` at every point of
`[0, t]` outside a finite set (no one-sided limits are required; boundedness is a separate
hypothesis wherever it is used). -/
def PiecewiseContinuousOn {E : Type*} [TopologicalSpace E] (Y : ℝ → E) (t : ℝ) : Prop :=
  ∃ S : Finset ℝ, ∀ s ∈ Icc 0 t, s ∉ S → ContinuousWithinAt Y (Icc 0 t) s

/-- `U` is a **time-ordered exponential** of `Y` on `[0, t]`: `U` is continuous on `[0, t]`,
`r ↦ U r * Y r` is integrable on `[0, t]`, and `U s = 1 + ∫₀ˢ U r * Y r dr` for `s ∈ [0, t]`
(the Volterra form of `U' = U Y`, `U 0 = 1`; later times multiply on the right). -/
def IsOrderedExp (Y U : ℝ → 𝔸) (t : ℝ) : Prop :=
  ContinuousOn U (Icc 0 t) ∧ IntervalIntegrable (fun r => U r * Y r) volume 0 t ∧
    ∀ s ∈ Icc 0 t, U s = 1 + ∫ r in (0 : ℝ)..s, U r * Y r

/-- The grid product `∏_{g < t M} (1 + M⁻¹ Y(g / M))` over the natural numbers `g < t M`
(that is, `g < ⌈t M⌉₊`), factors ordered by increasing `g` from left to right. -/
noncomputable def gridProd (Y : ℝ → 𝔸) (t : ℝ) (M : ℕ) : 𝔸 :=
  ((List.range ⌈t * M⌉₊).map fun g : ℕ => 1 + (M : ℝ)⁻¹ • Y (g / M)).prod

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

/-- **Finite matrices with the operator norm.** The time-ordered product limit for square
real matrices. -/
example {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {Y : ℕ → ℝ → Matrix n n ℝ} {Y₀ U : ℝ → Matrix n n ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hconv : TendstoUniformlyOn Y Y₀ atTop (Icc 0 t)) (hY₀ : PiecewiseContinuousOn Y₀ t)
    (hb : ∃ C, ∀ s ∈ Icc 0 t, ‖Y₀ s‖ ≤ C) (hU : IsOrderedExp Y₀ U t) :
    Tendsto (fun M : ℕ => gridProd (Y M) t M) atTop (𝓝 (U t)) := by
  apply _root_.NormedSpace.tendsto_gridProd_matrix <;> assumption

end Matrix

end MathlibExtTest.Analysis.Normed.Algebra.OrderedExponential
