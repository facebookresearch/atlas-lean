/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.GeneralizedTauPentagonalVanishing

namespace MathlibExtTest.NumberTheory.GeneralizedTauPentagonalVanishing

open MetaMathlibExt PowerSeries

private theorem pentagonal_le_four {t : ℤ} (ht : pentagonal t ≤ 4) :
    t = -1 ∨ t = 0 ∨ t = 1 := by
  have hp : t < 2 := by
    by_contra! h
    have h₁ := pentagonal_strictMonoOn.monotoneOn (show (2 : ℤ) ∈ Set.Ici 0 by decide)
      (show t ∈ Set.Ici 0 from le_trans (by decide : (0 : ℤ) ≤ 2) h) h
    have h₂ : pentagonal 2 = 5 := by norm_num [pentagonal_def]
    omega
  have hn : -2 < t := by
    by_contra! h
    have h₁ := pentagonal_strictAntiOn.antitoneOn
      (show t ∈ Set.Iic 0 from le_trans h (by decide : (-2 : ℤ) ≤ 0))
      (show (-2 : ℤ) ∈ Set.Iic 0 by decide) h
    have h₂ : pentagonal (-2) = 7 := by norm_num [pentagonal_def]
    omega
  omega

private theorem coeff_pentagonal_le_four {i : ℕ} (hi : i ≤ 4) :
    coeff i (pentagonalSeries ℤ) = if i = 0 then 1 else if i = 1 ∨ i = 2 then -1 else 0 := by
  by_cases h : i ∈ Set.range pentagonal
  · obtain ⟨t, rfl⟩ := h
    obtain rfl | rfl | rfl := pentagonal_le_four hi <;>
      rw [coeff_pentagonalSeries_pentagonal] <;> norm_num [pentagonal_def]
  · have h₀ : i ≠ 0 := fun e ↦ h ⟨0, (by norm_num [pentagonal_def] : pentagonal 0 = 0).trans e.symm⟩
    have h₁ : i ≠ 1 := fun e ↦ h ⟨1, (by norm_num [pentagonal_def] : pentagonal 1 = 1).trans e.symm⟩
    have h₂ : i ≠ 2 := fun e ↦ h ⟨-1, (by norm_num [pentagonal_def] : pentagonal (-1) = 2).trans e.symm⟩
    simp [coeff_pentagonalSeries_eq_zero ℤ h, h₀, h₁, h₂]

-- Compute the coefficient over the integers by finite multiplication, before reducing modulo p.
private theorem tau_eq_low_coeff_sum (k m : ℕ) (hm : m ≤ 4) :
    generalizedTau (k : ℤ) (m + 1) =
      ∑ l ∈ Finset.finsuppAntidiag (Finset.range k) m, ∏ i ∈ Finset.range k,
        if l i = 0 then 1 else if l i = 1 ∨ l i = 2 then -1 else 0 := by
  rw [generalizedTau_natCast, coeff_succ_X_mul, coeff_pow]
  apply Finset.sum_congr rfl
  intro l hl
  apply Finset.prod_congr rfl
  intro i hi
  have h := Finset.single_le_sum (f := fun j ↦ l j) (fun j _ ↦ Nat.zero_le (l j)) hi
  rw [(Finset.mem_finsuppAntidiag.mp hl).1] at h
  exact coeff_pentagonal_le_four (h.trans hm)

private theorem gap_four (t : ℤ) (ht : pentagonal t ≤ 4 - 1) :
    ¬ (6 - 1 : ℕ) ∣ 4 - 1 - pentagonal t := by
  obtain rfl | rfl | rfl := pentagonal_le_four (show pentagonal t ≤ 4 by omega) <;>
    norm_num [pentagonal_def]

private theorem gap_five (t : ℤ) (ht : pentagonal t ≤ 5 - 1) :
    ¬ (8 - 1 : ℕ) ∣ 5 - 1 - pentagonal t := by
  obtain rfl | rfl | rfl := pentagonal_le_four ht <;> norm_num [pentagonal_def]

-- The hypotheses hold at both tested indices; check the residues from the exact coefficients.
example : generalizedTau 6 4 ≡ 0 [ZMOD 5] := by
  have h : generalizedTau 6 4 = 10 := by
    change generalizedTau ((6 : ℕ) : ℤ) (3 + 1) = 10
    rw [tau_eq_low_coeff_sum 6 3 (by decide)]
    decide
  rw [h]
  decide

set_option maxRecDepth 4096 in
example : generalizedTau 8 5 ≡ 0 [ZMOD 7] := by
  have h : generalizedTau 8 5 = -70 := by
    change generalizedTau ((8 : ℕ) : ℤ) (4 + 1) = -70
    rw [tau_eq_low_coeff_sum 8 4 (by decide)]
    decide +kernel
  rw [h]
  decide

-- At the boundary n = 1, the pentagonal index t = 0 rules out the hypothesis.
example : pentagonal 0 ≤ 1 - 1 ∧ (6 - 1 : ℕ) ∣ 1 - 1 - pentagonal 0 := by
  norm_num [pentagonal_def]

example : ¬ generalizedTau 6 1 ≡ 0 [ZMOD 5] := by
  rw [generalizedTau_one]
  decide

-- Exercise the public theorem on both independently checked gaps.
example : generalizedTau 6 4 ≡ 0 [ZMOD 5] ∧ generalizedTau 8 5 ≡ 0 [ZMOD 7] :=
  ⟨generalizedTau_modEq_zero_of_pentagonal 4 (by decide) 6 (by decide) gap_four,
    generalizedTau_modEq_zero_of_pentagonal 5 (by decide) 8 (by decide) gap_five⟩

end MathlibExtTest.NumberTheory.GeneralizedTauPentagonalVanishing
