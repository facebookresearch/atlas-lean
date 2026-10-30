/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.Motifs.PWM
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

/-!
# Position weight matrix tests

Closed checks:
- DNA (`Fin 4`) with the uniform background: a deterministic column carries the maximal `2`
  bits and the uniform column `0` bits (the two ends of `[0, 2]`); a junk value of
  `infoContent` outside its domain (a zero background);
- the exact score distribution of a one-column `{0, 1}` matrix under a fair background;
- Berg–von Hippel at `λ = 0`: no selection returns the background;
- the Karlin–Altschul `λ` of the `+1 / -2` match/mismatch matrix on a uniform two-letter
  alphabet is `log φ` (golden ratio), and the target frequencies are a distribution;
- non-vacuity of the EM statements: a positive PWM (`PosPWM`), a covering data set of two
  sequences, and the OOPS and ZOOPS instances of `logLik_iterate_mStep_monotone`.

The definitions are real-valued and not executable.
-/

namespace Cslib.Bioinformatics.Motifs.PWM

open Real Cslib.MachineLearning.LatentVariable.ExpectationMaximization

/-! ## Information content on DNA -/

/-- The uniform background on four letters. -/
noncomputable abbrev unif4 : Fin 4 → ℝ := fun _ => ((Fintype.card (Fin 4) : ℝ))⁻¹

/-- A deterministic column carries `2` bits against the uniform DNA background. -/
example : infoContent (fun b => (PMF.pure (0 : Fin 4) b).toReal) unif4 = 2 := by
  rw [infoContent_uniform, InformationTheory.shannonEntropy_pure, sub_zero, Fintype.card_fin,
    show ((4 : ℕ) : ℝ) = 2 ^ (2 : ℕ) by norm_num, logb_pow, logb_self_eq_one one_lt_two]
  norm_num

/-- The uniform column carries `0` bits. -/
example : infoContent unif4 unif4 = 0 := by
  simp [infoContent]

/-- Every column carries at most `2` bits against the uniform DNA background. -/
example (P : PMF (Fin 4)) : infoContent (fun b => (P b).toReal) unif4 ≤ 2 :=
  infoContent_uniform_le_two (Fintype.card_fin 4) P

/-- Junk value outside the domain: against a zero background, `log (p / 0) = log 0 = 0`, so the
formula returns `0` although the divergence is infinite. The theorems assume `q > 0`. -/
example : infoContent (fun _ : Fin 2 => (1 / 2 : ℝ)) (fun _ => 0) = 0 := by
  simp [infoContent]

/-- The threshold test itself attains the Neyman–Pearson bound (a non-vacuous instance). -/
example (p : Fin 2 → Fin 4 → ℝ) (hp : ∀ i b, 0 < p i b) (t : ℝ) :
    ∑ s, (if t < score (logOdds p unif4) s then 1 else 0) * siteLik p s ≤
      ∑ s, (if t < score (logOdds p unif4) s then 1 else 0) * siteLik p s :=
  sum_mul_siteLik_le_of_sum_mul_bgLik_le hp (fun _ => by norm_num) t _
    (fun s => by split_ifs <;> norm_num) (fun s => by split_ifs <;> norm_num) le_rfl

/-! ## Exact score distribution -/

/-- The fair background on two letters. -/
noncomputable abbrev fair : Fin 2 → ℝ := fun _ => 1 / 2

/-- The one-column matrix scoring letter `b` as `b`. -/
abbrev idCol : Fin 1 → Fin 2 → ℤ := fun _ b => b.val

private lemma sum_fin1_fin2 (f : (Fin 1 → Fin 2) → ℝ) :
    ∑ s, f s = f (fun _ => 0) + f (fun _ => 1) := by
  rw [← (Equiv.funUnique (Fin 1) (Fin 2)).symm.sum_comp, Fin.sum_univ_two]
  rfl

/-- Score `1` has background probability `1/2`. -/
example : scoreDist fair idCol 1 = 1 / 2 := by
  rw [scoreDist_apply, Finset.sum_filter, sum_fin1_fin2]
  simp [score, bgLik]

/-- The p-value of the threshold `0` is `1`. -/
example : pValue fair idCol 0 = 1 := by
  rw [pValue_eq, Finset.sum_filter, sum_fin1_fin2]
  simp [score, bgLik]
  norm_num

/-! ## Berg–von Hippel -/

/-- With `λ = 0` (no selection), the Boltzmann PWM is the background. -/
example (ε : Fin 3 → Fin 4 → ℝ) (i : Fin 3) (b : Fin 4) :
    boltzmannPWM unif4 ε 0 i b = unif4 b := by
  simp [boltzmannPWM, partitionFn]

/-- The selected law of a concrete energy matrix is the Boltzmann product model. -/
example (s : Fin 2 → Fin 4) :
    selectedLaw unif4 (fun i b => (i.val : ℝ) * b.val) 1 s =
      siteLik (boltzmannPWM unif4 (fun i b => (i.val : ℝ) * b.val) 1) s :=
  selectedLaw_eq_siteLik _ _ _ s

/-! ## Karlin–Altschul `λ`: `+1` match, `-2` mismatch, uniform two letters -/

/-- Match `+1`, mismatch `-2`. -/
noncomputable abbrev matchScore : Fin 2 → Fin 2 → ℝ := fun a b => if a = b then 1 else -2

/-- The fair background is a distribution. -/
lemma isDist_fair : IsDist fair := ⟨fun _ => by norm_num, by simp⟩

/-- The fair background is positive. -/
lemma fair_pos : ∀ b, 0 < fair b := fun _ => by norm_num

/-- The expected score is `-1/2 < 0`. -/
lemma expected_matchScore_neg : ∑ a, ∑ b, fair a * fair b * matchScore a b < 0 := by
  simp [Fin.sum_univ_two]
  norm_num

/-- `λ = log φ`: `φ / 2 + φ⁻² / 2 = 1` because `φ² = φ + 1`. -/
lemma pairMGF_log_goldenRatio : pairMGF fair matchScore (log goldenRatio) = 1 := by
  have hφ : 0 < goldenRatio := goldenRatio_pos
  have h2 : goldenRatio ^ 2 = goldenRatio + 1 := goldenRatio_sq
  simp only [pairMGF, Fin.sum_univ_two, matchScore]
  simp only [Fin.isValue, ite_true, show ((0 : Fin 2) = 1) ↔ False by decide,
    show ((1 : Fin 2) = 0) ↔ False by decide, ite_false, mul_one]
  rw [show log goldenRatio * -2 = -log (goldenRatio ^ 2) by rw [log_pow]; push_cast; ring,
    exp_neg, exp_log hφ, exp_log (by positivity), h2]
  have hinv : (goldenRatio + 1)⁻¹ = 2 - goldenRatio :=
    inv_eq_of_mul_eq_one_right (by linear_combination (-1 : ℝ) * h2)
  simp only [fair, hinv]
  ring

/-- The Karlin–Altschul `λ` of this matrix is exactly `log φ`. -/
example : ∃! lam, 0 < lam ∧ pairMGF fair matchScore lam = 1 := by
  refine ⟨log goldenRatio, ⟨log_pos one_lt_goldenRatio, pairMGF_log_goldenRatio⟩, ?_⟩
  intro μ hμ
  obtain ⟨l, _, hl⟩ := existsUnique_pairMGF_eq_one isDist_fair (fun _ => by norm_num)
    expected_matchScore_neg ⟨0, 0, by norm_num [matchScore]⟩
  rw [hl μ hμ, hl _ ⟨log_pos one_lt_goldenRatio, pairMGF_log_goldenRatio⟩]

/-- Its target frequencies form a distribution with positive relative entropy. -/
example : IsDist (targetFreq fair matchScore (log goldenRatio)) ∧
    0 < ∑ ab, targetFreq fair matchScore (log goldenRatio) ab * matchScore ab.1 ab.2 :=
  ⟨isDist_targetFreq (fun _ => by norm_num) pairMGF_log_goldenRatio,
    sum_targetFreq_mul_pos isDist_fair (fun _ => by norm_num) ⟨0, 0, by norm_num [matchScore]⟩
      (log_pos one_lt_goldenRatio) pairMGF_log_goldenRatio⟩

/-! ## Motif EM: non-vacuity -/

/-- The uniform PWM of width `1` on two letters is a `PosPWM` (non-vacuity witness). -/
noncomputable def unifPWM : PosPWM 1 (Fin 2) :=
  ⟨fun _ _ => 1 / 2, fun _ _ => by norm_num, fun _ => by simp⟩

/-- Two sequences of length `2` (`n = 1`, `w = 1`): `01` and `10`. -/
def twoSeqs : Fin 2 → Fin (1 + 1) → Fin 2 := ![![0, 1], ![1, 0]]

/-- OOPS covers both letters. -/
lemma covers_oops : Covers (w := 1) (Z := Fin 2) some twoSeqs := by
  intro i b
  fin_cases i
  fin_cases b
  · exact ⟨0, 0, 0, rfl, rfl⟩
  · exact ⟨1, 0, 0, rfl, rfl⟩

/-- **OOPS**: the EM likelihood is monotone on this data set. -/
example :
    Monotone fun k => logLik (motifModel fair (fun _ : Fin 2 => 1 / 2) some) twoSeqs
      ((mStep fair_pos (prior := fun _ : Fin 2 => 1 / 2) (fun _ => by norm_num)
        covers_oops)^[k] unifPWM) :=
  logLik_iterate_mStep_monotone _ _ _ unifPWM

/-- The ZOOPS prior with `γ = 1/2`: `1/2` on no occurrence, `1/4` on each start. -/
noncomputable def zoopsPrior : Option (Fin 2) → ℝ
  | none => 1 / 2
  | some _ => 1 / 4

/-- ZOOPS covers both letters. -/
lemma covers_zoops : Covers (w := 1) (Z := Option (Fin 2)) id twoSeqs := by
  intro i b
  fin_cases i
  fin_cases b
  · exact ⟨0, some 0, 0, rfl, rfl⟩
  · exact ⟨1, some 0, 0, rfl, rfl⟩

/-- **ZOOPS**: the EM likelihood is monotone on this data set. -/
example :
    Monotone fun k => logLik (motifModel fair zoopsPrior id) twoSeqs
      ((mStep fair_pos (prior := zoopsPrior) (fun z => by cases z <;> norm_num [zoopsPrior])
        covers_zoops)^[k] unifPWM) :=
  logLik_iterate_mStep_monotone _ _ _ unifPWM

end Cslib.Bioinformatics.Motifs.PWM
