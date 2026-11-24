/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Combinatorics.RandomSubset
public import Mathlib.Analysis.SpecialFunctions.Exp

import MathlibExt.Probability.CorrelationInequalities.ReimerMixedMonotone
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Second Janson inequality

For containment events in an independent random subset, `janson_inequality_of_le` bounds the
probability of avoiding every event when the correlation sum is at least the expected count.
-/

@[expose] public section

open MeasureTheory unitInterval MathlibExt.Probability.Combinatorics.RandomSubset

namespace MathlibExt.Probability.JansonInequalityWanted

variable {α ι : Type*}

section Parameters

variable [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]

/-- **Expected number of contained sets (Janson's `μ`).** For a random subset `R` with element
probabilities `p` and sets `S i`, `μ = ∑ᵢ P(Sᵢ ⊆ R)` (Y. Zhao, *The Probabilistic Method in
Combinatorics*, MIT 18.218 notes, 2019, Setup 7.10). -/
noncomputable def jansonMu (p : α → I) (S : ι → Finset α) : ℝ :=
  ∑ i, (randomSubsetLaw p).real (containsEvent (S i))

/-- **Janson's correlation sum `Δ`.** `Δ = ∑ P(Sᵢ ⊆ R and Sⱼ ⊆ R)` over the ordered pairs
`(i, j)` with `i ≠ j` and `Sᵢ ∩ Sⱼ ≠ ∅` (Y. Zhao, *The Probabilistic Method in Combinatorics*,
MIT 18.218 notes, 2019, Setup 7.10). -/
noncomputable def jansonDelta (p : α → I) (S : ι → Finset α) : ℝ :=
  ∑ i, ∑ j, if i ≠ j ∧ ¬ Disjoint (S i) (S j) then
    (randomSubsetLaw p).real (containsEvent (S i) ∩ containsEvent (S j)) else 0

end Parameters

open Finset

section Subfamilies

private def miss (S : ι → Finset α) (s : Finset ι) : Set (α → Bool) :=
  {ω | ∀ j ∈ s, ω ∉ containsEvent (S j)}

private lemma miss_insert [DecidableEq ι] (S : ι → Finset α) (s : Finset ι) (i : ι) :
    miss S (insert i s) = miss S s \ containsEvent (S i) := by
  ext ω
  simp [miss, and_comm]

private lemma split_probability [Fintype α] [DecidableEq α] [DecidableEq ι]
    (p : α → I) (S : ι → Finset α) (s : Finset ι) (i : ι)
    (T : Finset α) :
    (randomSubsetLaw p).real (containsEvent T ∩ miss S (insert i s)) =
      (randomSubsetLaw p).real (containsEvent T ∩ miss S s) -
      (randomSubsetLaw p).real (containsEvent (T ∪ S i) ∩ miss S s) := by
  rw [miss_insert, ← containsEvent_inter]
  have h := measureReal_inter_add_sdiff (μ := randomSubsetLaw p)
    (s := containsEvent T ∩ miss S s) (measurableSet_containsEvent (S i))
  rw [Set.inter_sdiff_assoc, Set.inter_right_comm] at h
  linarith

-- After excluding another event, combine its support with U. Both remain disjoint from T.
private lemma disjoint_factor [Fintype α] [DecidableEq α]
    (p : α → I) (S : ι → Finset α) (s : Finset ι)
    (T U : Finset α) (hU : Disjoint T U) (hs : ∀ j ∈ s, Disjoint T (S j)) :
    (randomSubsetLaw p).real (containsEvent (T ∪ U) ∩ miss S s) =
      (randomSubsetLaw p).real (containsEvent T) *
        (randomSubsetLaw p).real (containsEvent U ∩ miss S s) := by
  classical
  induction s using Finset.induction_on generalizing U with
  | empty =>
    simp [miss, randomSubsetLaw_real_containsEvent, Finset.prod_union hU]
  | @insert i s hi ih =>
    have hs' := fun j hj => hs j (Finset.mem_insert_of_mem hj)
    rw [split_probability, split_probability, Finset.union_assoc,
      ih U hU hs', ih (U ∪ S i) (Finset.disjoint_union_right.mpr
        ⟨hU, hs i (Finset.mem_insert_self ..)⟩) hs', mul_sub]

open scoped Classical in
private lemma measureReal_filter [Fintype α] [DecidableEq α]
    (p : α → I) (A : Set (α → Bool)) (r : ℝ) :
    (∑ ω, if ω ∈ A then (randomSubsetLaw p).real {ω} * r else 0) =
      (randomSubsetLaw p).real A * r := by
  classical
  rw [← Finset.sum_filter, ← Finset.sum_mul, sum_measureReal_singleton]
  simp

private lemma harris [Fintype α] (p : α → I) {A B : Set (α → Bool)}
    (hA : StatMech.IsIncreasing A) (hB : StatMech.IsDecreasing B) :
    (randomSubsetLaw p).real (A ∩ B) ≤
      (randomSubsetLaw p).real A * (randomSubsetLaw p).real B := by
  classical
  let w (a : α) (b : Bool) : ℝ := if b then p a else 1 - (p a : ℝ)
  have hw (D : Set (α → Bool)) : StatMech.wprob w D = (randomSubsetLaw p).real D := by
    rw [← mul_one ((randomSubsetLaw p).real D), ← measureReal_filter]
    apply Finset.sum_congr rfl
    intro ω _
    by_cases h : ω ∈ D <;>
      simp [Set.indicator, h, StatMech.pweight, randomSubsetLaw_real_singleton, w]
  rw [← hw, ← hw, ← hw]
  apply StatMech.wprob_fkg_neg w _ _ hA hB
  · intro a b
    cases b
    · exact sub_nonneg.mpr (p a).2.2
    · exact (p a).2.1
  · intro a
    simp [w]

private lemma increasing_contains (T : Finset α) : StatMech.IsIncreasing (containsEvent T) := by
  intro x y hxy hx a ha
  exact Bool.eq_true_of_true_le (hx a ha ▸ hxy a)

private lemma decreasing_miss (S : ι → Finset α) (s : Finset ι) :
    StatMech.IsDecreasing (miss S s) := by
  intro x y hxy hx j hj hy
  exact hx j hj (increasing_contains _ hxy hy)

private noncomputable def pairMass [Fintype α] [DecidableEq α] [DecidableEq ι]
    (p : α → I) (S : ι → Finset α) (i j : ι) : ℝ :=
  if i ≠ j ∧ ¬ Disjoint (S i) (S j) then
    (randomSubsetLaw p).real (containsEvent (S i) ∩ containsEvent (S j)) else 0

private lemma pairMass_comm [Fintype α] [DecidableEq α] [DecidableEq ι]
    (p : α → I) (S : ι → Finset α) (i j : ι) :
    pairMass p S i j = pairMass p S j i := by
  simp only [pairMass, ne_comm (a := i) (b := j), disjoint_comm (a := S i) (b := S j),
    Set.inter_comm (containsEvent (S i)) (containsEvent (S j))]

variable [Fintype α] [DecidableEq α] [DecidableEq ι]

-- When i is added, separate its neighbors from the events independent of it.
private lemma insert_bound (p : α → I) (S : ι → Finset α) (s : Finset ι) (i : ι) (hi : i ∉ s) :
    (randomSubsetLaw p).real (miss S (insert i s)) ≤ (randomSubsetLaw p).real (miss S s) *
      Real.exp (-(randomSubsetLaw p).real (containsEvent (S i)) + ∑ j ∈ s, pairMass p S i j) := by
  classical
  let μ := randomSubsetLaw p
  let A (j : ι) := containsEvent (S j)
  let N := s.filter fun j => ¬ Disjoint (S i) (S j)
  let C := miss S (s.filter fun j => Disjoint (S i) (S j))
  have hsub : miss S s ⊆ C := fun _ h j hj => h j (Finset.mem_filter.mp hj).1
  have hind : μ.real (A i ∩ C) = μ.real (A i) * μ.real C := by
    simpa [μ, A, C, containsEvent] using
      disjoint_factor p S (s.filter fun j => Disjoint (S i) (S j)) (S i) ∅
        (Finset.disjoint_empty_right _) (fun _ hj => (Finset.mem_filter.mp hj).2)
  have hcover : A i ∩ C ⊆ (A i ∩ miss S s) ∪ ⋃ j ∈ N, (A i ∩ A j) ∩ C := by
    rintro ω ⟨hiω, hC⟩
    by_cases hm : ω ∈ miss S s
    · exact Or.inl ⟨hiω, hm⟩
    · simp only [miss, Set.mem_ofPred_eq, not_forall, not_not] at hm
      obtain ⟨j, hj, hA⟩ := hm
      have hn : j ∈ N := mem_filter.mpr ⟨hj, fun hd => hC j (mem_filter.mpr ⟨hj, hd⟩) hA⟩
      exact Or.inr (Set.mem_iUnion₂.mpr ⟨j, hn, ⟨hiω, hA⟩, hC⟩)
  have hsum : ∑ j ∈ N, μ.real (A i ∩ A j) = ∑ j ∈ s, pairMass p S i j := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hij : i ≠ j := fun e => hi (e ▸ hj)
    simp [pairMass, hij, A, μ]
  have herr : μ.real (⋃ j ∈ N, (A i ∩ A j) ∩ C) ≤
      (∑ j ∈ s, pairMass p S i j) * μ.real C := calc
    _ ≤ ∑ j ∈ N, μ.real ((A i ∩ A j) ∩ C) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ j ∈ N, μ.real (A i ∩ A j) * μ.real C := by
      exact Finset.sum_le_sum fun j _ => harris p
        ((increasing_contains (S i)).inter (increasing_contains (S j))) (decreasing_miss S _)
    _ = _ := by rw [← Finset.sum_mul, hsum]
  have hprob := (measureReal_mono (μ := μ) hcover).trans
    ((measureReal_union_le _ _).trans (add_le_add_right herr _))
  rw [hind] at hprob
  let d := μ.real (A i) - ∑ j ∈ s, pairMass p S i j
  have hcond : d * μ.real (miss S s) ≤ μ.real (A i ∩ miss S s) := by
    by_cases hd : 0 ≤ d
    · refine (mul_le_mul_of_nonneg_left (measureReal_mono hsub) hd).trans ?_
      dsimp [d]
      linarith
    · exact (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hd) measureReal_nonneg).trans
        measureReal_nonneg
  have hsplit := measureReal_inter_add_sdiff (μ := μ) (s := miss S s)
    (measurableSet_containsEvent (S i))
  rw [Set.inter_comm] at hsplit
  change μ.real (miss S (insert i s)) ≤ _
  rw [miss_insert]
  calc
    _ ≤ μ.real (miss S s) * (1 + (-d)) := by
      change _ + μ.real (miss S s \ A i) = _ at hsplit
      linarith
    _ ≤ μ.real (miss S s) * Real.exp (-d) :=
      mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (-d)]) measureReal_nonneg
    _ = _ := by simp [d, μ, A, sub_eq_add_neg, add_comm]

private lemma subfamily_bound (p : α → I) (S : ι → Finset α) (s : Finset ι) :
    (randomSubsetLaw p).real (miss S s) ≤
      Real.exp (-(∑ i ∈ s, (randomSubsetLaw p).real (containsEvent (S i))) +
        (∑ i ∈ s, ∑ j ∈ s, pairMass p S i j) / 2) := by
  induction s using Finset.induction_on with
  | empty => simp [miss]
  | @insert i s hi ih =>
    refine (insert_bound p S s i hi).trans
      ((mul_le_mul_of_nonneg_right ih (Real.exp_nonneg _)).trans_eq ?_)
    have hsymm : ∑ j ∈ s, pairMass p S j i = ∑ j ∈ s, pairMass p S i j :=
      Finset.sum_congr rfl fun j _ => pairMass_comm p S j i
    have hdiag : pairMass p S i i = 0 := by simp [pairMass]
    rw [← Real.exp_add]
    congr 1
    simp only [Finset.sum_insert hi, Finset.sum_add_distrib, hdiag, hsymm]
    ring

variable [Fintype ι]

-- The probability of keeping all of T in an independently sampled subfamily is q ^ #T.
open scoped Classical in
private lemma retention_mass (q : I) (T : Finset ι) (r : ℝ) :
    (∑ ω : ι → Bool, if ω ∈ containsEvent T then
        (randomSubsetLaw (fun _ : ι => q)).real {ω} * r else 0) =
      (q : ℝ) ^ T.card * r := by
  classical
  have hm := measureReal_filter (fun _ : ι => q) (containsEvent T) r
  rw [randomSubsetLaw_real_containsEvent, Finset.prod_const] at hm
  exact hm

-- Average the exponent of the subfamily bound. The logarithm of the full avoidance
-- probability is a common lower bound for all these exponents.
private lemma thinning_bound (p : α → I) (S : ι → Finset α) (q : I) :
    (randomSubsetLaw p).real {ω | ∀ i, ω ∉ containsEvent (S i)} ≤
      Real.exp (-(q : ℝ) * jansonMu p S + (q : ℝ) ^ 2 * jansonDelta p S / 2) := by
  classical
  let P := (randomSubsetLaw p).real {ω | ∀ i, ω ∉ containsEvent (S i)}
  by_cases hP : 0 < P
  · apply (Real.log_le_iff_le_exp hP).mp
    let a (i : ι) := (randomSubsetLaw p).real (containsEvent (S i))
    let b := pairMass p S
    let kept (ω : ι → Bool) := univ.filter fun i => ω i = true
    let w (ω : ι → Bool) := (randomSubsetLaw (fun _ : ι => q)).real {ω}
    have hw : ∑ ω, w ω = 1 := by simp [w]
    have hsingle : (∑ ω, w ω * ∑ i ∈ kept ω, a i) = (q : ℝ) * ∑ i, a i := by
      simp only [kept, Finset.sum_filter, Finset.mul_sum, mul_ite, mul_zero]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      simpa [w, containsEvent] using retention_mass q {i} (a i)
    have hpair : (∑ ω, w ω * ∑ i ∈ kept ω, ∑ j ∈ kept ω, b i j) =
        (q : ℝ) ^ 2 * ∑ i, ∑ j, b i j := by
      simp only [kept, Finset.sum_filter, Finset.ite_sum_zero, Finset.mul_sum, mul_ite, mul_zero]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hij : i = j
      · subst j
        simp [b, pairMass]
      · simpa [w, hij, ite_and, containsEvent] using retention_mass q {i, j} (b i j)
    have hlog (ω : ι → Bool) : Real.log P ≤
        -(∑ i ∈ kept ω, a i) + (∑ i ∈ kept ω, ∑ j ∈ kept ω, b i j) / 2 := by
      apply (Real.log_le_iff_le_exp hP).mpr
      exact (measureReal_mono (μ := randomSubsetLaw p)
        (show {x | ∀ i, x ∉ containsEvent (S i)} ⊆ miss S (kept ω) from
          fun _ hx i _ => hx i)).trans (subfamily_bound p S (kept ω))
    have havg := Finset.sum_le_sum (s := univ) fun ω _ =>
      mul_le_mul_of_nonneg_left (hlog ω) (show 0 ≤ w ω from measureReal_nonneg)
    rw [← Finset.sum_mul, hw, one_mul] at havg
    simp only [mul_add, mul_neg, ← mul_div_assoc, Finset.sum_add_distrib,
      Finset.sum_neg_distrib, ← Finset.sum_div, hsingle, hpair] at havg
    simpa only [neg_mul, jansonMu, jansonDelta, a, b, pairMass] using havg
  · exact (le_of_not_gt hP).trans (Real.exp_nonneg _)

end Subfamilies

variable [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]

/-- **Second Janson inequality.** In the setting of the first Janson inequality, if `Δ ≥ μ`
then `P(no Aᵢ occurs) ≤ exp(-μ² / (2Δ))` (Y. Zhao, *The Probabilistic Method in
Combinatorics*, MIT 18.218 notes, 2019, Theorem 7.14). -/
theorem janson_inequality_of_le (p : α → I) (S : ι → Finset α)
    (h : jansonMu p S ≤ jansonDelta p S) :
    (randomSubsetLaw p).real {ω | ∀ i, ω ∉ containsEvent (S i)} ≤
      Real.exp (-(jansonMu p S ^ 2 / (2 * jansonDelta p S))) := by
  have hμ : 0 ≤ jansonMu p S := Finset.sum_nonneg fun _ _ => measureReal_nonneg
  rcases (hμ.trans h).eq_or_lt with hzero | hpos
  · rw [← hzero]
    simp
  · let q : I := ⟨jansonMu p S / jansonDelta p S, div_nonneg hμ hpos.le,
        (div_le_one hpos).mpr h⟩
    refine (thinning_bound p S q).trans_eq ?_
    congr 1
    dsimp [q]
    field_simp
    ring

end MathlibExt.Probability.JansonInequalityWanted
