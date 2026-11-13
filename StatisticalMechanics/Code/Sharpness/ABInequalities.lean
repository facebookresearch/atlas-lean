/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/














































































import Code.Inequalities.Russo
import Code.Inequalities.BK
import Code.Foundations.CylinderDeriv
import Code.Sharpness.AizenmanBarsky

open MeasureTheory Set Finset
open scoped NNReal ENNReal






set_option linter.unusedVariables false

namespace StatMech

namespace Sharpness

open ConfigSpace StatMech

variable {E : Type*} [Fintype E] [DecidableEq E]



























theorem pivotalProb_le_of_disjointOccurrence
    {p : ℝ≥0} (hp : p ≤ 1) {A B C : Set (ConfigSpace E)} (hA : IsIncreasing A)
    (hB : IsIncreasing B) (hC : IsIncreasing C)
    (hpiv : {ω | IsPivotal e A ω} ⊆ disjointOccurrence B C) :
    pivotalProb (p : ℝ) A e ≤ prob (p : ℝ) B * prob (p : ℝ) C := by
  
  
  have hpivprob : pivotalProb (p : ℝ) A e = prob (p : ℝ) {ω | IsPivotal e A ω} := rfl
  rw [hpivprob]
  
  set μ := bernoulliProductMeasure (E := E) p hp with hμ
  have hpiveq : prob (p : ℝ) {ω | IsPivotal e A ω} = μ.real {ω | IsPivotal e A ω} :=
    (finiteRealProb_eq_prob p hp {ω | IsPivotal e A ω}).symm
  have hBeq : prob (p : ℝ) B = μ.real B := (finiteRealProb_eq_prob p hp B).symm
  have hCeq : prob (p : ℝ) C = μ.real C := (finiteRealProb_eq_prob p hp C).symm
  rw [hpiveq, hBeq, hCeq]
  
  calc μ.real {ω | IsPivotal e A ω}
      ≤ μ.real (disjointOccurrence B C) := measureReal_mono hpiv (measure_ne_top _ _)
    _ ≤ μ.real B * μ.real C := bk_inequality hp hB hC



























theorem deriv_prob_le_sum_bk
    {p : ℝ≥0} (hp : p ≤ 1) {A : Set (ConfigSpace E)} (hA : IsIncreasing A)
    (B C : E → Set (ConfigSpace E))
    (hB : ∀ e, IsIncreasing (B e)) (hC : ∀ e, IsIncreasing (C e))
    (hpiv : ∀ e, {ω | IsPivotal e A ω} ⊆ disjointOccurrence (B e) (C e)) :
    deriv (fun q => prob q A) (p : ℝ)
      ≤ ∑ e, prob (p : ℝ) (B e) * prob (p : ℝ) (C e) := by
  rw [deriv_prob_eq_sum_pivotalProb A hA]
  apply Finset.sum_le_sum
  intro e _
  exact pivotalProb_le_of_disjointOccurrence hp hA (hB e) (hC e) (hpiv e)











































theorem ab_hu_of_russo_bk {ι : Type*} (s : Finset ι)
    (dMdβ dMdh M J : ℝ) (Jcoef infl piv : ι → ℝ)
    (hMnn : 0 ≤ M) (hJnn : ∀ e ∈ s, 0 ≤ Jcoef e) (hinflnn : ∀ e ∈ s, 0 ≤ infl e)
    (hrusso : dMdβ = ∑ e ∈ s, piv e)
    (hbk : ∀ e ∈ s, piv e ≤ Jcoef e * M * infl e)
    (hJsum : ∑ e ∈ s, Jcoef e = J)
    (hinfl_eq : ∑ e ∈ s, infl e = dMdh)
    (hJle : ∀ e ∈ s, Jcoef e ≤ J) (hJ0 : 0 ≤ J) (hdMdh_nn : 0 ≤ dMdh) :
    dMdβ ≤ J * (M * dMdh) := by
  rw [hrusso]
  
  
  calc ∑ e ∈ s, piv e
      ≤ ∑ e ∈ s, J * M * infl e := by
        apply Finset.sum_le_sum
        intro e he
        calc piv e ≤ Jcoef e * M * infl e := hbk e he
          _ ≤ J * M * infl e := by
            apply mul_le_mul_of_nonneg_right _ (hinflnn e he)
            exact mul_le_mul_of_nonneg_right (hJle e he) hMnn
    _ = J * (M * ∑ e ∈ s, infl e) := by rw [Finset.mul_sum]; rw [Finset.mul_sum]; ring_nf
    _ = J * (M * dMdh) := by rw [hinfl_eq]






















theorem ab_eq6_of_russo_meanfield (β dMdβ M pivsum : ℝ) (hβ : 0 < β)
    (hrusso : dMdβ = pivsum)
    (hlb : (1 / β) * (1 - M) ≤ pivsum) :
    1 - M ≤ β * dMdβ := by
  rw [hrusso]
  
  have hmul : β * ((1 / β) * (1 - M)) ≤ β * pivsum :=
    mul_le_mul_of_nonneg_left hlb (le_of_lt hβ)
  have hsimp : β * ((1 / β) * (1 - M)) = 1 - M := by
    field_simp
  linarith [hmul, hsimp.symm.le, hsimp.le]
















theorem aizenmanBarskyInequality_of_russo_bk (M : ℝ → ℝ → ℝ) (J : ℝ) (hJ0 : 0 ≤ J)
    (hbuild : ∀ β h, ∃ (ι : Type) (s : Finset ι) (Jcoef infl piv : ι → ℝ),
      (0 ≤ M β h) ∧ (∀ e ∈ s, 0 ≤ Jcoef e) ∧ (∀ e ∈ s, 0 ≤ infl e) ∧
      (deriv (fun β => M β h) β = ∑ e ∈ s, piv e) ∧
      (∀ e ∈ s, piv e ≤ Jcoef e * M β h * infl e) ∧
      (∑ e ∈ s, Jcoef e = J) ∧
      (∑ e ∈ s, infl e = deriv (fun h => M β h) h) ∧
      (∀ e ∈ s, Jcoef e ≤ J) ∧ (0 ≤ deriv (fun h => M β h) h)) :
    AizenmanBarskyInequality M J := by
  intro β h
  obtain ⟨ι, s, Jcoef, infl, piv, hMnn, hJnn, hinflnn, hrusso, hbk, hJsum,
    hinfl_eq, hJle, hdMdh_nn⟩ := hbuild β h
  exact ab_hu_of_russo_bk s _ _ (M β h) J Jcoef infl piv hMnn hJnn hinflnn hrusso
    hbk hJsum hinfl_eq hJle hJ0 hdMdh_nn






theorem eq6_of_russo_meanfield (M : ℝ → ℝ → ℝ) (βc : ℝ) (hβc : 0 < βc)
    (hbuild : ∀ h ∈ Ici (0 : ℝ), ∃ pivsum : ℝ,
      (deriv (fun β => M β h) βc = pivsum) ∧
      ((1 / βc) * (1 - M βc h) ≤ pivsum)) :
    ∀ h ∈ Ici (0 : ℝ), 1 - M βc h ≤ βc * deriv (fun β => M β h) βc := by
  intro h hh
  obtain ⟨pivsum, hrusso, hlb⟩ := hbuild h hh
  exact ab_eq6_of_russo_meanfield βc _ (M βc h) pivsum hβc hrusso hlb













theorem ab_inequalities_discharged (M : ℝ → ℝ → ℝ) (J βc : ℝ) (hJ0 : 0 ≤ J)
    (hβc : 0 < βc)
    (hhu : ∀ β h, ∃ (ι : Type) (s : Finset ι) (Jcoef infl piv : ι → ℝ),
      (0 ≤ M β h) ∧ (∀ e ∈ s, 0 ≤ Jcoef e) ∧ (∀ e ∈ s, 0 ≤ infl e) ∧
      (deriv (fun β => M β h) β = ∑ e ∈ s, piv e) ∧
      (∀ e ∈ s, piv e ≤ Jcoef e * M β h * infl e) ∧
      (∑ e ∈ s, Jcoef e = J) ∧
      (∑ e ∈ s, infl e = deriv (fun h => M β h) h) ∧
      (∀ e ∈ s, Jcoef e ≤ J) ∧ (0 ≤ deriv (fun h => M β h) h))
    (h6 : ∀ h ∈ Ici (0 : ℝ), ∃ pivsum : ℝ,
      (deriv (fun β => M β h) βc = pivsum) ∧
      ((1 / βc) * (1 - M βc h) ≤ pivsum)) :
    AizenmanBarskyInequality M J ∧
      (∀ h ∈ Ici (0 : ℝ), 1 - M βc h ≤ βc * deriv (fun β => M β h) βc) :=
  ⟨aizenmanBarskyInequality_of_russo_bk M J hJ0 hhu, eq6_of_russo_meanfield M βc hβc h6⟩

end Sharpness

end StatMech
