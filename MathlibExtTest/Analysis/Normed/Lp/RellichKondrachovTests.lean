/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Normed.Lp.RellichKondrachov
public import MathlibExt.Analysis.Normed.Lp.Compactness

/-!
# Tests for the weighted Rellich sequence model

* The unit vector `e₀` lies in `rellichBall 1` over `ℝ`, and `2 • e₃`
  lies in `rellichBall 7` over `ℂ` (weighted sum `10 * 4 = 40 ≤ 49`).
* The two-coordinate combination `3 • e₀ + 4 • e₁` lies in `rellichBall 7`
  over `ℝ` (weighted sum `9 + 2 * 16 = 41 ≤ 49`).
* The norm bound and the tail estimate on `e₀`.
* Total boundedness, compactness, and the sequential form on concrete balls.
* Original finite-sum tail/span contracts and canonical truncation equivalence.
* Canonical truncation norm bounds and compactness-criterion hypotheses.
* `#print axioms` for the main theorems: standard triple only.
-/

open MathlibExt.Analysis.Normed.Lp.RellichKondrachov
open MathlibExt.Analysis.Normed.Lp.Compactness
open scoped lp ENNReal Topology

namespace MathlibExtTest.Analysis.Normed.Lp.RellichKondrachovTests

/-- The unit vector `e₀` has weighted sum `1 * 1 = 1 ≤ 1 ^ 2`. -/
private theorem single_zero_mem :
    lp.single 2 0 (1 : ℝ) ∈ rellichBall (𝕜 := ℝ) 1 := by
  apply memRellichBall_of_support (S := {0}) _ _
  · intro n hn
    by_contra hnot
    apply hn
    exact lp.single_apply_ne (E := fun _ : ℕ => ℝ) (p := 2) (i := 0) (a := (1 : ℝ))
      (by simpa using hnot)
  · simp [Finset.sum_singleton, rellichWeight]

/-- `2 • e₃` over `ℂ` has weighted sum `(1 + 9) * 4 = 40 ≤ 7 ^ 2`. -/
private theorem single_three_mem :
    lp.single 2 3 (2 : ℂ) ∈ rellichBall (𝕜 := ℂ) 7 := by
  apply memRellichBall_of_support (S := {3}) _ _
  · intro n hn
    by_contra hnot
    apply hn
    exact lp.single_apply_ne (E := fun _ : ℕ => ℂ) (p := 2) (i := 3) (a := (2 : ℂ))
      (by simpa using hnot)
  · simp [Finset.sum_singleton, rellichWeight]
    norm_num [Complex.norm_ofNat]

/-- `3 • e₀ + 4 • e₁` has weighted sum `9 + 2 * 16 = 41 ≤ 7 ^ 2`. -/
private theorem two_coord_mem :
    lp.single 2 0 (3 : ℝ) + lp.single 2 1 (4 : ℝ) ∈ rellichBall (𝕜 := ℝ) 7 := by
  apply memRellichBall_of_support (S := {0, 1}) _ _
  · intro n hn
    by_contra hnot
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
    apply hn
    simp [Pi.single_eq_of_ne hnot.1, Pi.single_eq_of_ne hnot.2]
  · rw [Finset.sum_insert (by simp), Finset.sum_singleton]
    have e0 : ((lp.single 2 0 (3 : ℝ) + lp.single 2 1 (4 : ℝ) : ℓ²(ℕ, ℝ)) : ℕ → ℝ) 0 = 3 := by
      simp
    have e1 : ((lp.single 2 0 (3 : ℝ) + lp.single 2 1 (4 : ℝ) : ℓ²(ℕ, ℝ)) : ℕ → ℝ) 1 = 4 := by
      simp
    rw [e0, e1]
    norm_num [rellichWeight]

/-- Norm bound on `e₀` via the Rellich ball. -/
example : ‖(lp.single 2 0 (1 : ℝ) : ℓ²(ℕ, ℝ))‖ ≤ 1 :=
  norm_le_of_memRellichBall zero_le_one single_zero_mem

/-- Tail estimate on `e₀` with `N = 1`: the truncation already equals `e₀`,
so the left side is `0 ≤ 1 / 2`. -/
example : ‖(lp.single 2 0 (1 : ℝ) : ℓ²(ℕ, ℝ)) -
    lpTrunc 2 1 (lp.single 2 0 (1 : ℝ))‖ ^ 2 ≤ 1 / 2 := by
  calc ‖(lp.single 2 0 (1 : ℝ) : ℓ²(ℕ, ℝ)) -
        lpTrunc 2 1 (lp.single 2 0 (1 : ℝ))‖ ^ 2
      ≤ (1 : ℝ) ^ 2 / rellichWeight 1 := norm_sub_lpTrunc_sq_le single_zero_mem 1
    _ = 1 / 2 := by simp [rellichWeight]; norm_num

/-- Total boundedness on a concrete ball. -/
example : TotallyBounded (rellichBall (𝕜 := ℝ) 3) := totallyBounded_rellichBall 3

/-- Compactness on a concrete complex ball. -/
example : IsCompact (rellichBall (𝕜 := ℂ) 2) := isCompact_rellichBall 2

/-- The sequential form on the constant sequence at `e₀`. -/
example : ∃ y ∈ rellichBall (𝕜 := ℝ) 1, ∃ φ : ℕ → ℕ, StrictMono φ ∧
    Filter.Tendsto ((fun _ => lp.single 2 0 (1 : ℝ)) ∘ φ) Filter.atTop (𝓝 y) :=
  exists_subseq_tendsto_of_memRellichBall 1 (fun _ => single_zero_mem)

/-- The complex `2 • e₃` example also satisfies the norm bound. -/
example : ‖(lp.single 2 3 (2 : ℂ) : ℓ²(ℕ, ℂ))‖ ≤ 7 :=
  norm_le_of_memRellichBall (by norm_num) single_three_mem

/-- The two-coordinate example also satisfies the norm bound. -/
example : ‖(lp.single 2 0 (3 : ℝ) + lp.single 2 1 (4 : ℝ) : ℓ²(ℕ, ℝ))‖ ≤ 7 :=
  norm_le_of_memRellichBall (by norm_num) two_coord_mem

section Characterization

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The original finite sum is definitionally the canonical truncation at `p = 2`. -/
example (N : ℕ) (x : ℓ²(ℕ, 𝕜)) :
    (∑ i ∈ Finset.range N, lp.single 2 i ((x : ℕ → 𝕜) i)) = lpTrunc 2 N x :=
  rfl

/-- Canonical truncations preserve the norm bound on every Rellich ball. -/
example {x : ℓ²(ℕ, 𝕜)} {M : ℝ} (hM : 0 ≤ M) (hx : memRellichBall x M) (N : ℕ) :
    ‖lpTrunc 2 N x‖ ≤ M :=
  (norm_lpTrunc_le N x).trans (norm_le_of_memRellichBall hM hx)

/-- Every real radius satisfies both hypotheses of the canonical compactness criterion. -/
example (M : ℝ) : Bornology.IsBounded (rellichBall (𝕜 := 𝕜) M) ∧
    UniformTailVanishing 2 (rellichBall (𝕜 := 𝕜) M) :=
  (totallyBounded_iff_bounded_and_uniformTailVanishing (p := 2) (by norm_num)).mp
    (totallyBounded_rellichBall M)

/-- The finite-sum truncation has exactly the original shifted-tail norm. -/
example (N : ℕ) (x : ℓ²(ℕ, 𝕜)) :
    ‖x - (∑ i ∈ Finset.range N, lp.single 2 i ((x : ℕ → 𝕜) i))‖ ^ 2 =
      ∑' n, ‖(x : ℕ → 𝕜) (n + N)‖ ^ 2 :=
  norm_sub_lpTrunc_sq_eq N

/-- The finite-sum tail keeps the original weighted bound for every real radius. -/
example {x : ℓ²(ℕ, 𝕜)} {M : ℝ} (hx : memRellichBall x M) (N : ℕ) :
    ‖x - (∑ i ∈ Finset.range N, lp.single 2 i ((x : ℕ → 𝕜) i))‖ ^ 2 ≤
      M ^ 2 / rellichWeight N :=
  norm_sub_lpTrunc_sq_le hx N

/-- The finite-sum truncation keeps the original span-membership statement. -/
example (N : ℕ) (x : ℓ²(ℕ, 𝕜)) :
    (∑ i ∈ Finset.range N, lp.single 2 i ((x : ℕ → 𝕜) i)) ∈
      Submodule.span 𝕜
        ((fun i : ℕ => lp.single (E := fun _ : ℕ => 𝕜) 2 i (1 : 𝕜)) ''
          (Finset.range N : Set ℕ)) :=
  lpTrunc_mem_span N x

end Characterization

#print axioms isCompact_rellichBall

#print axioms totallyBounded_rellichBall

end MathlibExtTest.Analysis.Normed.Lp.RellichKondrachovTests
