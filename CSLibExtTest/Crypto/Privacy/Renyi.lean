/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import CSLibExt.Crypto.Privacy.Renyi

/-!
# Tests for Rényi differential privacy

* Mironov's Corollary 3: sensitivity `1` and noise variance `σ²` give `(α, α / (2 σ²))`-RDP.
* The mechanism stated as the law of `f x + Z` with `Z ∼ N(0, v)`.
* The budget is attained: for the identity query on neighbours at distance `1`, a smaller `ε`
  fails.
* At order `1`, under the convention that `renyiDiv` is `⊤` at orders `α ≤ 1`, no mechanism is
  Rényi differentially private once two inputs are neighbours.
-/

open MeasureTheory ProbabilityTheory MathlibExt.InformationTheory.RenyiDivergence
  Cslib.Crypto.Privacy
open scoped NNReal

namespace CSLibExtTest.Crypto.Privacy.Renyi

-- Mironov's Corollary 3: a real-valued query of sensitivity `1` with noise `N(0, σ²)`.
example {X : Type*} {Adj : X → X → Prop} {f : X → ℝ}
    (hf : ∀ ⦃x y⦄, Adj x y → |f x - f y| ≤ 1) {σ : ℝ} (hσ : σ ≠ 0) {α : ℝ} (hα : 1 < α) :
    RenyiDifferentiallyPrivate Adj (fun x ↦ gaussianReal (f x) (σ ^ 2).toNNReal) α
      (α / (2 * σ ^ 2)) := by
  have h := gaussianMechanism_renyiDifferentiallyPrivate hf
    (v := (σ ^ 2).toNNReal) (by simpa [Real.toNNReal_eq_zero] using hσ) hα
  rwa [Real.coe_toNNReal _ (sq_nonneg σ), one_pow, mul_one] at h

-- The output law of `f x + Z` for `Z ∼ N(0, v)` is the mechanism's `gaussianReal (f x) v`.
example {X : Type*} {Adj : X → X → Prop} {f : X → ℝ} {Δ : ℝ}
    (hf : ∀ ⦃x y⦄, Adj x y → |f x - f y| ≤ Δ) {v : ℝ≥0} (hv : v ≠ 0) {α : ℝ} (hα : 1 < α) :
    RenyiDifferentiallyPrivate Adj (fun x ↦ (gaussianReal 0 v).map (fun z ↦ f x + z)) α
      (α * Δ ^ 2 / (2 * v)) := by
  simp_rw [gaussianReal_map_const_add, zero_add]
  exact gaussianMechanism_renyiDifferentiallyPrivate hf hv hα

-- The identity query on the reals, neighbours at distance at most `1`, order `2`, unit variance.
example : RenyiDifferentiallyPrivate (fun x y : ℝ ↦ |x - y| ≤ 1) (fun x ↦ gaussianReal x 1) 2 1 := by
  simpa using gaussianMechanism_renyiDifferentiallyPrivate (f := id)
    (Adj := fun x y : ℝ ↦ |x - y| ≤ 1) (fun x y h ↦ h) one_ne_zero (by norm_num : (1 : ℝ) < 2)

-- The budget `1` above cannot be lowered to `1 / 2`: the neighbours `1` and `0` attain it.
example : ¬RenyiDifferentiallyPrivate (fun x y : ℝ ↦ |x - y| ≤ 1) (fun x ↦ gaussianReal x 1) 2
    (1 / 2) := by
  intro h
  have h₁ := h (x := 1) (y := 0) (by norm_num)
  rw [renyiDiv_gaussianReal 1 0 one_ne_zero (by norm_num), EReal.coe_le_coe_iff] at h₁
  norm_num at h₁

-- At order `1` the divergence is `⊤` by the convention of `renyiDiv` at orders `α ≤ 1`, so no
-- budget works once two inputs are neighbours.
example (ε : ℝ) :
    ¬RenyiDifferentiallyPrivate (fun _ _ : Unit ↦ True) (fun _ ↦ gaussianReal 0 1) 1 ε := by
  intro h
  have h₁ := h (x := ()) (y := ()) trivial
  rw [renyiDiv_of_le_one le_rfl] at h₁
  exact absurd h₁ (by simp)

end CSLibExtTest.Crypto.Privacy.Renyi
