/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.LSeries.OesterleFundamentalIdentity

/-!
# Oesterlé's fundamental identity API checks

The integrand unfolds to the expression of Oesterlé's (3.1.1), the Euler factor bound holds at
`p = 2`, and the main theorem applies to the degenerate instance `ψ = 0`, `g = δ`
(so `G = 1`), all Euler coefficients `0`, `F = F₁ = 0`, `d = M = 1` and `σ = 2`.
-/

@[expose] public section

open Complex MeasureTheory MetaMathlibExt.OesterleFundamentalIdentity

example (d M : ℝ) (ψ : ℕ → ℂ) (H : ℂ → ℂ) (σ t : ℝ) :
    oesterleIntegrand d M ψ H σ t =
      (d : ℂ) ^ ((σ : ℂ) + t * I - 1) * ((M : ℂ) ^ ((σ : ℂ) + t * I) *
        Gamma ((σ : ℂ) + t * I) ^ 2) * LSeries ψ ((σ : ℂ) + t * I) * H ((σ : ℂ) + t * I) *
        (((σ : ℂ) + t * I - 1) ^ 3)⁻¹ :=
  rfl

/-- The Euler factor bound at `p = 2`. -/
example {α β α' β' : ℕ → ℂ}
    (hC2 : ∀ p : ℕ, p.Prime → ‖α p‖ ≤ √p ∧ ‖β p‖ ≤ √p ∧ ‖α' p‖ ≤ √p ∧ ‖β' p‖ ≤ √p)
    {s : ℂ} (hs : 3 / 2 < s.re) : ‖eulerFactor α β α' β' 2 s‖ ≤ 11 :=
  norm_eulerFactor_le hC2 Nat.prime_two hs

lemma eulerFactor_zero (p : ℕ) (s : ℂ) : eulerFactor 0 0 0 0 p s = 1 := by
  simp [eulerFactor]

lemma rapidDecay_zero (S : Set ℝ) : RapidDecayInStrips (fun _ => 0) S :=
  fun _ _ _ _ => ⟨0, 0, fun _ _ _ _ => by simp⟩

lemma lSeriesSummable_delta (s : ℂ) : LSeriesSummable LSeries.delta s :=
  (hasSum_single 1 fun n hn => by simp [LSeries.term_def, LSeries.delta, hn]).summable

/-- The degenerate instance of `oesterle_fundamental_identity`. -/
example (U : ℝ) (hU : 1 ≤ U) :
    oesterleIntegral 1 1 0 (LSeries LSeries.delta) 2 = 0 ∧
      oesterleIntegral 1 1 0 (partialEuler 0 0 0 0 U) 2 =
        -oesterleIntegral 1 1 0 (fun s => LSeries LSeries.delta s - partialEuler 0 0 0 0 U s) 2 := by
  have h := oesterle_fundamental_identity (d := 1) (M := 1) (ψ := 0) (g := LSeries.delta)
    (α := 0) (β := 0) (α' := 0) (β' := 0) one_pos one_pos
    (fun s _ => LSeriesSummable_zero) (fun s _ => lSeriesSummable_delta s)
    (fun s _ => by simp [eulerFactor_zero, LSeries_delta])
    (fun p _ => by simp [Real.sqrt_nonneg])
    (fun _ => 0) (differentiable_const 0) (fun s _ => by simp)
    (rapidDecay_zero _) (fun _ => rfl) ⟨fun _ => 0, differentiable_const 0, fun _ => by simp⟩
    ⟨Set.univ, fun _ => 0, isOpen_univ, Set.subset_univ _, differentiableOn_const 0,
      fun s _ => by simp, by simpa using rapidDecay_zero (Set.Ici 1)⟩
    (by norm_num : (3 / 2 : ℝ) < 2)
  exact ⟨h.1, (h.2.1 U hU).2.2⟩
