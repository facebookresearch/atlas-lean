/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Percolation.Universality.RSWConstantMaintenance

/-!
# Crossings of `kn × n` rectangles by induction on `k`

`rai_cross μ n k` is the probability of the left–right crossing of `[0, kn] × [0, n]`. Gluing the
crossing of `[0, kn] × [0, n]` to a crossing of `[(k - 1)n, (k + 1)n] × [0, n]` through the band
`[(k - 1)n, kn] × [0, n]` gives `rai_cross μ n k ≥ β (γ/2)^(k - 1)`, where `β` bounds the square
crossing, `γ` bounds the `2n × n` crossings and `1/2` bounds the band crossings. The `2n × n`
bound `γ` is the Russo–Seymour–Welsh input and is a hypothesis here.

## Main definitions

* `StatMech.Universality.rai_cross`.

## Main results

* `StatMech.Universality.rai_step`, `StatMech.Universality.rai_cross_lb`,
  `StatMech.Universality.rai_cross_pos`.
-/

@[expose] public section

open Set MeasureTheory SimpleGraph
open scoped ENNReal NNReal

namespace StatMech

namespace Universality

open StatMech.Lattice
open StatMech.RSW.Box
open StatMech.RSW.Strip

variable (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ]

/-- The probability of the left–right crossing of `[0, kn] × [0, n]`. -/
noncomputable def rai_cross (n : ℤ) (k : ℕ) : ℝ :=
  μ.real (horizontalCrossingEvent 0 ((k : ℤ) * n) 0 n)

omit [IsProbabilityMeasure μ] in
@[simp] theorem rai_cross_def (n : ℤ) (k : ℕ) :
    rai_cross μ n k = μ.real (horizontalCrossingEvent 0 ((k : ℤ) * n) 0 n) := rfl

/-- One induction step: from `cL ≤ rai_cross μ n k`, `γ` on `[(k - 1)n, (k + 1)n] × [0, n]` and
`1/2`
on the band, `cL · (1/2) · γ ≤ rai_cross μ n (k + 1)`. -/
theorem rai_step (hpa : PositivelyAssociated μ) {n : ℤ} (hn : 0 < n)
    {k : ℕ} (hk : 1 ≤ k) {cL γ : ℝ} (hcL0 : 0 ≤ cL) (hγ0 : 0 ≤ γ)
    (hL : cL ≤ rai_cross μ n k)
    (h2box : γ ≤ μ.real (horizontalCrossingEvent (((k : ℤ) - 1) * n) (((k : ℤ) + 1) * n) 0 n))
    (hband : (1 : ℝ) / 2 ≤ μ.real (verticalCrossingEvent (((k : ℤ) - 1) * n) ((k : ℤ) * n) 0 n)) :
    cL * (1 / 2) * γ ≤ rai_cross μ n (k + 1) := by
  have hk1 : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  have ham : (0 : ℤ) ≤ ((k : ℤ) - 1) * n := by positivity
  have hmm' : ((k : ℤ) - 1) * n ≤ (k : ℤ) * n := by nlinarith
  have hm'b : (k : ℤ) * n ≤ ((k : ℤ) + 1) * n := by nlinarith
  have hamL : (0 : ℤ) < (k : ℤ) * n := by positivity
  have hmbR : ((k : ℤ) - 1) * n < ((k : ℤ) + 1) * n := by nlinarith
  have hcd : (0 : ℤ) ≤ n := le_of_lt hn
  have hL' : cL ≤ μ.real (horizontalCrossingEvent 0 ((k : ℤ) * n) 0 n) := hL
  have hstep := rcm_aspect_step μ hpa ham hmm' hm'b hamL hmbR hcd hcL0 hγ0 hL' h2box hband
  have hconv : ((k : ℤ) + 1) * n = (((k + 1 : ℕ) : ℤ)) * n := by push_cast; ring
  rw [rai_cross_def]
  rw [hconv] at hstep
  exact hstep

/-- `β (γ/2)^(k - 1) ≤ rai_cross μ n k` for all `k ≥ 1`, given the square bound `β`, the bound `γ`
on
all `2n × n` crossings `[(k - 1)n, (k + 1)n] × [0, n]` and the band bound `1/2`. -/
theorem rai_cross_lb (hpa : PositivelyAssociated μ) {n : ℤ} (hn : 0 < n)
    {β γ : ℝ} (hβ : 0 < β) (hγ : 0 < γ)
    (hseed : β ≤ rai_cross μ n 1)
    (h2box : ∀ k : ℕ, 1 ≤ k →
      γ ≤ μ.real (horizontalCrossingEvent (((k : ℤ) - 1) * n) (((k : ℤ) + 1) * n) 0 n))
    (hband : ∀ k : ℕ, 1 ≤ k →
      (1 : ℝ) / 2 ≤ μ.real (verticalCrossingEvent (((k : ℤ) - 1) * n) ((k : ℤ) * n) 0 n)) :
    ∀ k : ℕ, 1 ≤ k → β * ((1 / 2) * γ) ^ (k - 1) ≤ rai_cross μ n k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    simpa using hseed
  | succ k hk ih =>
    have hck0 : (0 : ℝ) ≤ β * ((1 / 2) * γ) ^ (k - 1) := by positivity
    have hstep := rai_step μ hpa hn hk hck0 (le_of_lt hγ) ih
      (h2box k hk) (hband k hk)
    have hexp : (k + 1) - 1 = (k - 1) + 1 := by omega
    rw [hexp, pow_succ]
    calc β * (((1 / 2) * γ) ^ (k - 1) * ((1 / 2) * γ))
        = β * ((1 / 2) * γ) ^ (k - 1) * (1 / 2) * γ := by ring
      _ ≤ rai_cross μ n (k + 1) := hstep

/-- Positivity form of `rai_cross_lb`. -/
theorem rai_cross_pos (hpa : PositivelyAssociated μ) {n : ℤ} (hn : 0 < n)
    {β γ : ℝ} (hβ : 0 < β) (hγ : 0 < γ)
    (hseed : β ≤ rai_cross μ n 1)
    (h2box : ∀ k : ℕ, 1 ≤ k →
      γ ≤ μ.real (horizontalCrossingEvent (((k : ℤ) - 1) * n) (((k : ℤ) + 1) * n) 0 n))
    (hband : ∀ k : ℕ, 1 ≤ k →
      (1 : ℝ) / 2 ≤ μ.real (verticalCrossingEvent (((k : ℤ) - 1) * n) ((k : ℤ) * n) 0 n)) :
    ∀ k : ℕ, 1 ≤ k → ∃ c : ℝ, 0 < c ∧ c ≤ rai_cross μ n k := by
  intro k hk
  refine ⟨β * ((1 / 2) * γ) ^ (k - 1), ?_, rai_cross_lb μ hpa hn hβ hγ hseed h2box hband k hk⟩
  positivity

end Universality

end StatMech
