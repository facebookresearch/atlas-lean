/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Phylogenetics.GTRIdentifiability

/-!
# Tests for GTR identifiability

Non-vacuity witness: F81 on `Fin 4` with base frequencies `(0.1, 0.2, 0.3, 0.4)` and all
exchangeabilities `1` lies in the GTR domain, and the identifiability theorems apply to it.
Symmetry witnesses: changing the diagonal of `s` does not change the rate matrix; doubling `s`
and halving the branch length leaves the pair-site law unchanged while the off-diagonal
exchangeabilities differ (so one branch of unknown length cannot identify `s`); swapping two
states relabels the pair-site law. Boundary case: with zero exchangeabilities (outside the
domain) the rate matrix is `0` for every `π`, so `π` is not identified.
-/

@[expose] public section

open Finset Matrix ProbabilityTheory MathlibExt.Biology.Phylogenetics.SubstitutionModels

namespace MathlibExtTest.Biology.Phylogenetics.GTRIdentifiability

open MathlibExt.Biology.Phylogenetics.GTRIdentifiability

/-- Base frequencies `(0.1, 0.2, 0.3, 0.4)`. -/
noncomputable def π₀ : Fin 4 → ℝ := ![1 / 10, 2 / 10, 3 / 10, 4 / 10]

/-- All exchangeabilities `1` (F81). -/
def s₀ : Matrix (Fin 4) (Fin 4) ℝ := Matrix.of fun _ _ => 1

theorem isGTRParam₀ : IsGTRParam π₀ s₀ where
  pos i := by fin_cases i <;> norm_num [π₀]
  sum_eq_one := by norm_num [π₀, Fin.sum_univ_four]
  symm _ _ := rfl
  offDiag_pos _ _ _ := by norm_num [s₀]

/-- The rate matrix recovers the base frequencies (non-vacuous use of `gtrRate_eq_iff`). -/
example {π' : Fin 4 → ℝ} {s' : Matrix (Fin 4) (Fin 4) ℝ} (hp' : IsGTRParam π' s')
    (h : gtrRate π₀ s₀ = gtrRate π' s') : π' 3 = 4 / 10 := by
  rw [← ((gtrRate_eq_iff isGTRParam₀ hp').1 h).1]
  simp [π₀]

/-- The rate matrix recovers the off-diagonal exchangeabilities. -/
example {π' : Fin 4 → ℝ} {s' : Matrix (Fin 4) (Fin 4) ℝ} (hp' : IsGTRParam π' s')
    (h : gtrRate π₀ s₀ = gtrRate π' s') : s' 0 2 = 1 :=
  (((gtrRate_eq_iff isGTRParam₀ hp').1 h).2 0 2 (by decide)).symm

/-- `eq_of_gtrRate_eq` needs no positivity of the second parameter. -/
example {π' : Fin 4 → ℝ} {s' : Matrix (Fin 4) (Fin 4) ℝ} (hπ' : ∑ i, π' i = 1)
    (hs' : ∀ i j, s' i j = s' j i) (h : gtrRate π₀ s₀ = gtrRate π' s') : π' = π₀ :=
  (eq_of_gtrRate_eq isGTRParam₀ hπ' hs' h).symm

/-- Symmetry 1: the diagonal of `s` is invisible. -/
example : gtrRate π₀ (s₀ + diagonal fun _ => 5) = gtrRate π₀ s₀ :=
  gtrRate_congr_offDiag π₀ fun i j h => by simp [h]

/-- Symmetry 2: rate and time are confounded at one branch: `(2 • s₀, 1)` and `(s₀, 2)` have
the same pair-site law, but different exchangeabilities. -/
example : gtrPairLaw π₀ ((2 : ℝ) • s₀) 1 = gtrPairLaw π₀ s₀ 2 := by
  rw [gtrPairLaw_smul, mul_one]

example : ((2 : ℝ) • s₀) 0 1 ≠ s₀ 0 1 := by norm_num [s₀]

/-- One branch identifies `t * s`: the scaled pair is recovered from the law. -/
example {π' : Fin 4 → ℝ} {s' : Matrix (Fin 4) (Fin 4) ℝ} {t' : ℝ} (hp' : IsGTRParam π' s')
    (ht' : 0 < t') (h : gtrPairLaw π₀ s₀ 2 = gtrPairLaw π' s' t') : t' * s' 0 1 = 2 := by
  have := ((gtrPairLaw_eq_iff isGTRParam₀ hp' two_pos ht').1 h).2 0 1 (by decide)
  simpa [s₀] using this.symm

/-- With a known branch length, the pair-site law identifies `s` exactly. -/
example {π' : Fin 4 → ℝ} {s' : Matrix (Fin 4) (Fin 4) ℝ} (hp' : IsGTRParam π' s')
    (h : gtrPairLaw π₀ s₀ 1 = gtrPairLaw π' s' 1) : π' = π₀ ∧ s' 1 3 = 1 := by
  obtain ⟨h1, h2⟩ := eq_and_offDiag_eq_of_gtrPairLaw_eq isGTRParam₀ hp' one_pos h
  exact ⟨h1.symm, (h2 1 3 (by decide)).symm⟩

/-- The transition function on `t ≥ 0` identifies the parameters. -/
example {π' : Fin 4 → ℝ} {s' : Matrix (Fin 4) (Fin 4) ℝ} (hp' : IsGTRParam π' s')
    (h : ∀ t, 0 ≤ t → ctmcTransition (gtrRate π₀ s₀) t = ctmcTransition (gtrRate π' s') t) :
    π' = π₀ :=
  (eq_and_offDiag_eq_of_ctmcTransition_eq isGTRParam₀ hp' h).1.symm

/-- The pair-site law is a probability distribution. -/
example (t : ℝ) : ∑ i, ∑ j, gtrPairLaw π₀ s₀ t i j = 1 := sum_sum_gtrPairLaw isGTRParam₀ t

example {t : ℝ} (ht : 0 ≤ t) : 0 ≤ gtrPairLaw π₀ s₀ t 0 3 := gtrPairLaw_nonneg isGTRParam₀ ht 0 3

/-- Symmetry 3: swapping states `0 ↔ 1` relabels the pair-site law. -/
example (t : ℝ) :
    gtrPairLaw (π₀ ∘ Equiv.swap 0 1) (s₀.submatrix (Equiv.swap 0 1) (Equiv.swap 0 1)) t 0 2 =
      gtrPairLaw π₀ s₀ t 1 2 := by
  rw [gtrPairLaw_comp_perm, Equiv.swap_apply_left,
    Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]

/-- Under an unknown relabeling, the base frequencies are recovered up to that relabeling. -/
example {π' : Fin 4 → ℝ} {s' : Matrix (Fin 4) (Fin 4) ℝ} (hp' : IsGTRParam π' s')
    (h : ∀ i j, gtrPairLaw π₀ s₀ 1 (Equiv.swap 0 1 i) (Equiv.swap 0 1 j) =
      gtrPairLaw π' s' 1 i j) : π' 0 = 2 / 10 := by
  rw [(eq_comp_perm_of_gtrPairLaw_eq isGTRParam₀ hp' one_pos one_pos _ h).1]
  simp [π₀]

/-- The rate-level relabeling theorem. -/
example {π' : Fin 4 → ℝ} {s' : Matrix (Fin 4) (Fin 4) ℝ} (hp' : IsGTRParam π' s')
    (h : (gtrRate π₀ s₀).submatrix (Equiv.swap 0 1) (Equiv.swap 0 1) = gtrRate π' s') :
    π' 1 = 1 / 10 := by
  rw [(eq_comp_perm_of_gtrRate_submatrix_eq isGTRParam₀ hp' _ h).1]
  simp [π₀]

/-- Boundary: with zero exchangeabilities (outside the domain) `π` is not identified. -/
example : gtrRate π₀ 0 = gtrRate (fun _ => 1 / 4) (0 : Matrix (Fin 4) (Fin 4) ℝ) ∧
    π₀ ≠ fun _ => 1 / 4 := by
  refine ⟨by ext i j; simp [gtrRate], fun h => ?_⟩
  have := congrFun h 0
  norm_num [π₀] at this

/-- K80 determines `κ`. -/
example {κ : ℝ} (h : k80Rate κ = k80Rate 2) : κ = 2 := k80Rate_injective h

end MathlibExtTest.Biology.Phylogenetics.GTRIdentifiability
