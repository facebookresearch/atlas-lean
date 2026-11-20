/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





































































































import Mathlib
import Code.Ising.InfiniteVolume
import Code.Foundations.StochasticDomination
import Code.Inequalities.FKG

open scoped BigOperators ENNReal StatMech
open StatMech.Ising StatMech.Lattice Finset MeasureTheory Set

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace StatMech

namespace Ising

variable {d : ℕ}









theorem spinB_mono (p q : Bool) (h : p ≤ q) :
    (if p then (1 : ℝ) else -1) ≤ (if q then 1 else -1) := by
  cases p <;> cases q <;> simp_all (config := { decide := true })


theorem spinB_inf (p q : Bool) :
    (if (p ⊓ q) then (1 : ℝ) else -1) = min (if p then 1 else -1) (if q then 1 else -1) := by
  cases p <;> cases q <;> norm_num


theorem spinB_sup (p q : Bool) :
    (if (p ⊔ q) then (1 : ℝ) else -1) = max (if p then 1 else -1) (if q then 1 else -1) := by
  cases p <;> cases q <;> norm_num









theorem glue_mono_interior (η : ConfigSpace (Site d)) {n : ℕ}
    (τ τ' : {x // x ∈ box d n} → Bool) (h : τ ≤ τ') : glue η τ ≤ glue η τ' := by
  intro x
  by_cases hx : x ∈ box d n
  · rw [glue_mem _ _ hx, glue_mem _ _ hx]; exact h ⟨x, hx⟩
  · rw [glue_not_mem _ _ hx, glue_not_mem _ _ hx]



theorem glue_mono_boundary {n : ℕ} (η η' : ConfigSpace (Site d)) (hle : η ≤ η')
    (τ : {x // x ∈ box d n} → Bool) : glue η τ ≤ glue η' τ := by
  intro x
  by_cases hx : x ∈ box d n
  · rw [glue_mem _ _ hx, glue_mem _ _ hx]
  · rw [glue_not_mem _ _ hx, glue_not_mem _ _ hx]; exact hle x











theorem spin_glue_inf (n : ℕ) (η η' : ConfigSpace (Site d)) (hle : η ≤ η')
    (a b : {x // x ∈ box d n} → Bool) (x : Site d) :
    spin (glue η (a ⊓ b)) x = min (spin (glue η a) x) (spin (glue η' b) x) := by
  by_cases hx : x ∈ box d n
  · simp only [spin, glue_mem _ _ hx, Pi.inf_apply]; exact spinB_inf _ _
  · simp only [spin, glue_not_mem _ _ hx]
    conv_lhs => rw [show η x = η x ⊓ η' x from (inf_eq_left.mpr (hle x)).symm]
    exact spinB_inf _ _



theorem spin_glue_sup (n : ℕ) (η η' : ConfigSpace (Site d)) (hle : η ≤ η')
    (a b : {x // x ∈ box d n} → Bool) (x : Site d) :
    spin (glue η' (a ⊔ b)) x = max (spin (glue η a) x) (spin (glue η' b) x) := by
  by_cases hx : x ∈ box d n
  · simp only [spin, glue_mem _ _ hx, Pi.sup_apply]; exact spinB_sup _ _
  · simp only [spin, glue_not_mem _ _ hx]
    conv_lhs => rw [show η' x = η x ⊔ η' x from (sup_eq_right.mpr (hle x)).symm]
    exact spinB_sup _ _





theorem prod_supermod (u₁ u₂ v₁ v₂ : ℝ) :
    u₁ * v₁ + u₂ * v₂ ≤ min u₁ u₂ * min v₁ v₂ + max u₁ u₂ * max v₁ v₂ := by
  rcases le_total u₁ u₂ with hu | hu <;> rcases le_total v₁ v₂ with hv | hv <;>
    simp only [min_eq_left, min_eq_right, max_eq_left, max_eq_right, hu, hv] <;>
    nlinarith [hu, hv]








theorem bond_glue_supermod (n : ℕ) (η η' : ConfigSpace (Site d)) (hle : η ≤ η')
    (a b : {x // x ∈ box d n} → Bool) (e : Sym2 (Site d)) :
    bond (glue η a) e + bond (glue η' b) e
      ≤ bond (glue η (a ⊓ b)) e + bond (glue η' (a ⊔ b)) e := by
  induction e using Sym2.inductionOn with
  | hf x y =>
    simp only [bond_mk]
    rw [spin_glue_inf n η η' hle a b x, spin_glue_inf n η η' hle a b y,
        spin_glue_sup n η η' hle a b x, spin_glue_sup n η η' hle a b y]
    exact prod_supermod _ _ _ _






theorem spin_glue_add (n : ℕ) (η η' : ConfigSpace (Site d)) (hle : η ≤ η')
    (a b : {x // x ∈ box d n} → Bool) (x : Site d) :
    spin (glue η a) x + spin (glue η' b) x
      = spin (glue η (a ⊓ b)) x + spin (glue η' (a ⊔ b)) x := by
  rw [spin_glue_inf n η η' hle a b x, spin_glue_sup n η η' hle a b x]
  rcases le_total (spin (glue η a) x) (spin (glue η' b) x) with h | h
  · simp only [min_eq_left h, max_eq_right h]
  · simp only [min_eq_right h, max_eq_left h]; ring









theorem fvEnergy_supermod (n : ℕ) (B : Finset (Sym2 (Site d))) (h : ℝ) (hh : 0 ≤ h)
    (η η' : ConfigSpace (Site d)) (hle : η ≤ η')
    (a b : {x // x ∈ box d n} → Bool) :
    fvEnergy η n B h (a ⊓ b) + fvEnergy η' n B h (a ⊔ b)
      ≤ fvEnergy η n B h a + fvEnergy η' n B h b := by
  unfold fvEnergy
  have hbond : (∑ e ∈ B, bond (glue η a) e) + ∑ e ∈ B, bond (glue η' b) e
      ≤ (∑ e ∈ B, bond (glue η (a ⊓ b)) e) + ∑ e ∈ B, bond (glue η' (a ⊔ b)) e := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun e _ => bond_glue_supermod n η η' hle a b e)
  have hfield : (∑ x ∈ boxFinset d n, spin (glue η a) x) + ∑ x ∈ boxFinset d n, spin (glue η' b) x
      = (∑ x ∈ boxFinset d n, spin (glue η (a ⊓ b)) x)
        + ∑ x ∈ boxFinset d n, spin (glue η' (a ⊔ b)) x := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun x _ => spin_glue_add n η η' hle a b x)
  nlinarith [hbond, hfield, mul_le_mul_of_nonneg_left hbond hh]











theorem fvWeight_cross (n : ℕ) (B : Finset (Sym2 (Site d))) (β h : ℝ)
    (hβ : 0 ≤ β) (hh : 0 ≤ h) (η η' : ConfigSpace (Site d)) (hle : η ≤ η')
    (a b : {x // x ∈ box d n} → Bool) :
    fvWeight η n B β h a * fvWeight η' n B β h b
      ≤ fvWeight η n B β h (a ⊓ b) * fvWeight η' n B β h (a ⊔ b) := by
  unfold fvWeight
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hsm := fvEnergy_supermod n B h hh η η' hle a b
  nlinarith [mul_le_mul_of_nonneg_left hsm hβ]








theorem fvProb_cross (n : ℕ) (B : Finset (Sym2 (Site d))) (β h : ℝ)
    (hβ : 0 ≤ β) (hh : 0 ≤ h) (η η' : ConfigSpace (Site d)) (hle : η ≤ η')
    (a b : ConfigSpace {x // x ∈ box d n}) :
    fvProb η n B β h a * fvProb η' n B β h b
      ≤ fvProb η n B β h (a ⊓ b) * fvProb η' n B β h (a ⊔ b) := by
  unfold fvProb
  rw [div_mul_div_comm, div_mul_div_comm]
  exact (div_le_div_iff_of_pos_right
    (mul_pos (fvZ_pos η n B β h) (fvZ_pos η' n B β h))).mpr
    (fvWeight_cross n B β h hβ hh η η' hle a b)













theorem fvProb_dominates (n : ℕ) (B : Finset (Sym2 (Site d))) (β h : ℝ)
    (hβ : 0 ≤ β) (hh : 0 ≤ h) (η η' : ConfigSpace (Site d)) (hle : η ≤ η')
    {A : Set (ConfigSpace {x // x ∈ box d n})} (hA : IsIncreasing A) :
    (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * fvProb η n B β h ω)
      ≤ ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * fvProb η' n B β h ω := by
  refine holley_dominates (fun ω => fvProb_nonneg η n B β h ω)
    (fun ω => fvProb_nonneg η' n B β h ω) ?_ ?_ hA
  · rw [fvProb_sum_eq_one η n B β h, fvProb_sum_eq_one η' n B β h]
  · intro a b; exact fvProb_cross n B β h hβ hh η η' hle a b







theorem fvMeasure_real_eq (η : ConfigSpace (Site d)) (n : ℕ)
    (B : Finset (Sym2 (Site d))) (β h : ℝ) {A : Set (ConfigSpace (Site d))}
    (hA : MeasurableSet A) :
    (fvMeasure η n B β h).real A
      = ∑ τ : {x // x ∈ box d n} → Bool,
          fvProb η n B β h τ * (Set.indicator A (fun _ => (1 : ℝ)) (glue η τ)) := by
  unfold Measure.real
  rw [show (fvMeasure η n B β h) A
        = ∑ τ : {x // x ∈ box d n} → Bool,
            (ENNReal.ofReal (fvProb η n B β h τ) • Measure.dirac (glue η τ)) A from ?_]
  · rw [ENNReal.toReal_sum ?_]
    · apply Finset.sum_congr rfl
      intro τ _
      rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hA]
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (fvProb_nonneg η n B β h τ)]
      congr 1
      by_cases hmem : glue η τ ∈ A
      · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]; simp
      · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem]; simp
    · intro τ _
      rw [Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top (Measure.dirac (glue η τ)) A)
  · unfold fvMeasure
    exact Measure.finsetSum_apply Finset.univ _ A

















theorem fvMeasure_dominated (n : ℕ) (B : Finset (Sym2 (Site d))) (β h : ℝ)
    (hβ : 0 ≤ β) (hh : 0 ≤ h) (η η' : ConfigSpace (Site d)) (hle : η ≤ η') :
    (fvMeasure η n B β h) ≼ (fvMeasure η' n B β h) := by
  intro A hA hAinc
  rw [fvMeasure_real_eq η n B β h hA, fvMeasure_real_eq η' n B β h hA]
  set A₁ : Set (ConfigSpace {x // x ∈ box d n}) := (fun τ => glue η τ) ⁻¹' A with hA1
  set A₂ : Set (ConfigSpace {x // x ∈ box d n}) := (fun τ => glue η' τ) ⁻¹' A with hA2
  have hreη : ∀ τ : {x // x ∈ box d n} → Bool,
      Set.indicator A (fun _ => (1 : ℝ)) (glue η τ) = Set.indicator A₁ (fun _ => (1 : ℝ)) τ := by
    intro τ
    by_cases hmem : glue η τ ∈ A
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (show τ ∈ A₁ from hmem)]
    · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem (show τ ∉ A₁ from hmem)]
  have hreη' : ∀ τ : {x // x ∈ box d n} → Bool,
      Set.indicator A (fun _ => (1 : ℝ)) (glue η' τ) = Set.indicator A₂ (fun _ => (1 : ℝ)) τ := by
    intro τ
    by_cases hmem : glue η' τ ∈ A
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (show τ ∈ A₂ from hmem)]
    · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem (show τ ∉ A₂ from hmem)]
  simp_rw [hreη, hreη']
  have hA1inc : IsIncreasing A₁ := fun τ τ' hτ hmem => hAinc (glue_mono_interior η τ τ' hτ) hmem
  have hsub : A₁ ⊆ A₂ := fun τ hmem => hAinc (glue_mono_boundary η η' hle τ) hmem
  calc ∑ τ, fvProb η n B β h τ * Set.indicator A₁ (fun _ => (1 : ℝ)) τ
      = ∑ τ, Set.indicator A₁ (fun _ => (1 : ℝ)) τ * fvProb η n B β h τ := by
        apply Finset.sum_congr rfl; intro τ _; ring
    _ ≤ ∑ τ, Set.indicator A₁ (fun _ => (1 : ℝ)) τ * fvProb η' n B β h τ :=
        fvProb_dominates n B β h hβ hh η η' hle hA1inc
    _ ≤ ∑ τ, Set.indicator A₂ (fun _ => (1 : ℝ)) τ * fvProb η' n B β h τ := by
        apply Finset.sum_le_sum; intro τ _
        apply mul_le_mul_of_nonneg_right _ (fvProb_nonneg η' n B β h τ)
        by_cases h1 : τ ∈ A₁
        · rw [Set.indicator_of_mem h1, Set.indicator_of_mem (hsub h1)]
        · rw [Set.indicator_of_notMem h1]
          by_cases h2 : τ ∈ A₂
          · rw [Set.indicator_of_mem h2]; norm_num
          · rw [Set.indicator_of_notMem h2]
    _ = ∑ τ, fvProb η' n B β h τ * Set.indicator A₂ (fun _ => (1 : ℝ)) τ := by
        apply Finset.sum_congr rfl; intro τ _; ring










theorem minusField_le (η : ConfigSpace (Site d)) : minusField d ≤ η := by
  intro x; simp [minusField]


theorem le_plusField (η : ConfigSpace (Site d)) : η ≤ plusField d := by
  intro x; simp [plusField]






theorem fvMeasure_minusField_le (n : ℕ) (B : Finset (Sym2 (Site d))) (β h : ℝ)
    (hβ : 0 ≤ β) (hh : 0 ≤ h) (η : ConfigSpace (Site d)) :
    (fvMeasure (minusField d) n B β h) ≼ (fvMeasure η n B β h) :=
  fvMeasure_dominated n B β h hβ hh (minusField d) η (minusField_le η)






theorem fvMeasure_le_plusField (n : ℕ) (B : Finset (Sym2 (Site d))) (β h : ℝ)
    (hβ : 0 ≤ β) (hh : 0 ≤ h) (η : ConfigSpace (Site d)) :
    (fvMeasure η n B β h) ≼ (fvMeasure (plusField d) n B β h) :=
  fvMeasure_dominated n B β h hβ hh η (plusField d) (le_plusField η)















theorem fvMeasure_minus_sandwich_plus (n : ℕ) (B : Finset (Sym2 (Site d))) (β h : ℝ)
    (hβ : 0 ≤ β) (hh : 0 ≤ h) (η : ConfigSpace (Site d)) :
    (fvMeasure (minusField d) n B β h) ≼ (fvMeasure η n B β h)
    ∧ (fvMeasure η n B β h) ≼ (fvMeasure (plusField d) n B β h) :=
  ⟨fvMeasure_minusField_le n B β h hβ hh η, fvMeasure_le_plusField n B β h hβ hh η⟩






theorem fvMeasure_minus_le_plus (n : ℕ) (B : Finset (Sym2 (Site d))) (β h : ℝ)
    (hβ : 0 ≤ β) (hh : 0 ≤ h) :
    (fvMeasure (minusField d) n B β h) ≼ (fvMeasure (plusField d) n B β h) :=
  fvMeasure_dominated n B β h hβ hh (minusField d) (plusField d) (minusField_le (plusField d))

end Ising

end StatMech
