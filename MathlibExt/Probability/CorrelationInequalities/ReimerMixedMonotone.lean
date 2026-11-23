/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.CorrelationInequalities.Reimer
public import MathlibExt.Probability.CorrelationInequalities.ReimerCompression
public import MathlibExt.Probability.CorrelationInequalities.FKG

@[expose] public section

/-!
# Reimer's inequality for an increasing and a decreasing event

If `A` is increasing and `B` is decreasing, then `A □ B = A ∩ B` (`A` is witnessed by the open
coordinates of a configuration and `B` by its closed coordinates), and `A` and `B` are negatively
correlated by the FKG inequality. Hence `P(A □ B) ≤ P(A) P(B)` for such a pair.

## Main results

* `StatMech.wprob_fkg_pos`, `StatMech.wprob_fkg_neg`: the FKG (Harris) inequality for product
  probability weights, for two increasing events and for an increasing and a decreasing event.
* `StatMech.disjointOccurrence_eq_inter_of_mixed`: `A □ B = A ∩ B` for `A` increasing and `B`
  decreasing.
* `StatMech.reimerMixed_wprob`, `StatMech.reimerMixed_inequality`: Reimer's inequality for such a
  pair, for product weights and for `bernoulliProductMeasure p`.
-/

open MeasureTheory Finset
open scoped NNReal

namespace StatMech

open ConfigSpace

variable {E : Type*}

lemma wprob_eq_mass_mul_indicator [Fintype E] [DecidableEq E] (φ : E → Bool → ℝ)
    (S : Set (ConfigSpace E)) :
    wprob φ S = ∑ ω, pweight φ ω * S.indicator (fun _ => (1 : ℝ)) ω := by
  unfold wprob
  exact Finset.sum_congr rfl (fun ω _ => mul_comm _ _)

lemma wprob_add_compl [Fintype E] [DecidableEq E] (φ : E → Bool → ℝ)
    (hφ1 : ∀ x, φ x false + φ x true = 1) (B : Set (ConfigSpace E)) :
    wprob φ B + wprob φ Bᶜ = 1 := by
  rw [wprob_eq_mass_mul_indicator φ B, wprob_eq_mass_mul_indicator φ Bᶜ,
    ← Finset.sum_add_distrib]
  rw [show (∑ ω, (pweight φ ω * B.indicator (fun _ => (1 : ℝ)) ω
      + pweight φ ω * Bᶜ.indicator (fun _ => (1 : ℝ)) ω)) = ∑ ω, pweight φ ω from ?_]
  · exact sum_pweight_eq_one hφ1
  · refine Finset.sum_congr rfl (fun ω _ => ?_)
    by_cases h : ω ∈ B <;> simp [Set.indicator, h, Set.mem_compl_iff]

lemma wprob_inter_add_inter_compl [Fintype E] [DecidableEq E] (φ : E → Bool → ℝ)
    (A B : Set (ConfigSpace E)) :
    wprob φ (A ∩ B) + wprob φ (A ∩ Bᶜ) = wprob φ A := by
  unfold wprob
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  by_cases ha : ω ∈ A <;> by_cases hb : ω ∈ B <;>
    simp [Set.indicator, ha, hb, Set.mem_inter_iff, Set.mem_compl_iff]

lemma pweight_fkgLatticeCondition [Fintype E] (φ : E → Bool → ℝ) :
    FKGLatticeCondition (pweight φ) := by
  refine FKGLatticeCondition.of_logModular (fun ω ω' => ?_)
  unfold pweight
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun x _ => ?_)
  change φ x (ω x) * φ x (ω' x) = φ x ((ω ⊔ ω') x) * φ x ((ω ⊓ ω') x)
  simp only [Pi.sup_apply, Pi.inf_apply]
  cases ω x <;> cases ω' x <;> first | rfl | (simp; ring)

/-- The Harris–FKG inequality for a product probability weight: increasing events are positively
correlated. -/
theorem wprob_fkg_pos [Fintype E] [DecidableEq E] (φ : E → Bool → ℝ)
    (hφ0 : ∀ x b, 0 ≤ φ x b) (hφ1 : ∀ x, φ x false + φ x true = 1)
    {A B : Set (ConfigSpace E)} (hA : IsIncreasing A) (hB : IsIncreasing B) :
    wprob φ A * wprob φ B ≤ wprob φ (A ∩ B) := by
  have hπ0 : (0 : ConfigSpace E → ℝ) ≤ pweight φ := fun ω => pweight_nonneg hφ0 ω
  have hfkg := fkg_inequality_events (π := pweight φ) hπ0 (sum_pweight_eq_one hφ1)
    (pweight_fkgLatticeCondition φ) hA hB
  rw [wprob_eq_mass_mul_indicator φ A, wprob_eq_mass_mul_indicator φ B,
    wprob_eq_mass_mul_indicator φ (A ∩ B)]
  exact hfkg

/-- The Harris–FKG inequality for an increasing and a decreasing event: they are negatively
correlated. -/
theorem wprob_fkg_neg [Fintype E] [DecidableEq E] (φ : E → Bool → ℝ)
    (hφ0 : ∀ x b, 0 ≤ φ x b) (hφ1 : ∀ x, φ x false + φ x true = 1)
    {A B : Set (ConfigSpace E)} (hA : IsIncreasing A) (hB : IsDecreasing B) :
    wprob φ (A ∩ B) ≤ wprob φ A * wprob φ B := by
  have hpos := wprob_fkg_pos φ hφ0 hφ1 hA hB.compl
  have hdec := wprob_inter_add_inter_compl φ A B
  have hcompl := wprob_add_compl φ hφ1 B
  have hBc : wprob φ Bᶜ = 1 - wprob φ B := by linarith
  rw [hBc] at hpos
  nlinarith [hpos, hdec]

lemma occursOn_support_of_increasing {A : Set (ConfigSpace E)} (hA : IsIncreasing A)
    {ω : ConfigSpace E} (hω : ω ∈ A) : OccursOn A {e | ω e = true} ω := by
  intro ω' hω'
  refine hA (fun e => ?_) hω
  by_cases he : ω e = true
  · rw [hω' e he]
  · simp only [Bool.not_eq_true] at he; rw [he]; exact Bool.false_le _

lemma occursOn_cosupport_of_decreasing {B : Set (ConfigSpace E)} (hB : IsDecreasing B)
    {ω : ConfigSpace E} (hω : ω ∈ B) : OccursOn B {e | ω e = false} ω := by
  intro ω' hω'
  refine hB (fun e => ?_) hω
  by_cases he : ω e = false
  · rw [hω' e he]
  · simp only [Bool.not_eq_false] at he; rw [he]; exact Bool.le_true _

lemma disjoint_support_cosupport (ω : ConfigSpace E) :
    Disjoint ({e | ω e = true} : Set E) {e | ω e = false} := by
  rw [Set.disjoint_left]
  intro e he hf
  simp only [Set.mem_ofPred_eq] at he hf
  rw [he] at hf; exact Bool.noConfusion hf

/-- For `A` increasing and `B` decreasing, `A □ B = A ∩ B`. -/
theorem disjointOccurrence_eq_inter_of_mixed {A B : Set (ConfigSpace E)}
    (hA : IsIncreasing A) (hB : IsDecreasing B) :
    disjointOccurrence A B = A ∩ B := by
  refine Set.Subset.antisymm (disjointOccurrence_subset_inter A B) ?_
  rintro ω ⟨hAω, hBω⟩
  exact ⟨{e | ω e = true}, {e | ω e = false}, disjoint_support_cosupport ω,
    occursOn_support_of_increasing hA hAω, occursOn_cosupport_of_decreasing hB hBω⟩

/-- Reimer's inequality for an increasing and a decreasing event under a product probability
weight. -/
theorem reimerMixed_wprob [Fintype E] [DecidableEq E] (φ : E → Bool → ℝ)
    (hφ0 : ∀ x b, 0 ≤ φ x b) (hφ1 : ∀ x, φ x false + φ x true = 1)
    {A B : Set (ConfigSpace E)} (hA : IsIncreasing A) (hB : IsDecreasing B) :
    wprob φ (disjointOccurrence A B) ≤ wprob φ A * wprob φ B := by
  rw [disjointOccurrence_eq_inter_of_mixed hA hB]
  exact wprob_fkg_neg φ hφ0 hφ1 hA hB

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- Reimer's inequality for an increasing and a decreasing event under the product Bernoulli
measure. -/
theorem reimerMixed_inequality [Fintype E] [DecidableEq E] {p : ℝ≥0} (hp : p ≤ 1)
    {A B : Set (ConfigSpace E)} (hA : IsIncreasing A) (hB : IsDecreasing B) :
    (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B)
      ≤ (bernoulliProductMeasure (E := E) p hp).real A
        * (bernoulliProductMeasure (E := E) p hp).real B := by
  set φ : E → Bool → ℝ := fun (_ : E) (b : Bool) => (bernoulliMeasure p hp).real {b} with hφ
  have hφ0 : ∀ x b, 0 ≤ φ x b := fun _ _ => measureReal_nonneg
  have hφ1 : ∀ x, φ x false + φ x true = 1 := fun _ => bernoulliMeasure_real_false_add_true hp
  rw [bernoulli_real_eq_wprob hp (disjointOccurrence A B), bernoulli_real_eq_wprob hp A,
    bernoulli_real_eq_wprob hp B]
  exact reimerMixed_wprob φ hφ0 hφ1 hA hB

end StatMech
