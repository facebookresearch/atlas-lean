/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/









import Code.FrontierB.FiniteCurrentConditionalPMF

open MeasureTheory
open scoped ENNReal BigOperators

namespace StatMech.FrontierB

def boolSupport {I : Type*} [Fintype I] [DecidableEq I]
    (b : I → Bool) : Finset I := Finset.univ.filter fun i => b i

def boolAvoid {I : Type*} [Fintype I] [DecidableEq I]
    (T : Finset I) : Set (I → Bool) :=
  {b | Disjoint (boolSupport b) T}

theorem boolSupport_injective {I : Type*} [Fintype I] [DecidableEq I] :
    Function.Injective (boolSupport : (I → Bool) → Finset I) := by
  intro a b h
  funext i
  have hi := Finset.ext_iff.mp h i
  simp [boolSupport] at hi
  cases hai : a i <;> cases hbi : b i <;> simp_all

theorem mem_boolAvoid_compl_support_iff {I : Type*}
    [Fintype I] [DecidableEq I] (a b : I → Bool) :
    a ∈ boolAvoid (Finset.univ \ boolSupport b) ↔
      boolSupport a ⊆ boolSupport b := by
  simp only [boolAvoid, Set.mem_setOf_eq]
  rw [Finset.disjoint_left]
  constructor
  · intro h x hxa
    by_contra hxb
    exact h hxa (by simp [hxb])
  · intro hsub x hxa hxb
    exact (Finset.mem_sdiff.mp hxb).2 (hsub hxa)

def boolLower {I : Type*} [Fintype I] [DecidableEq I]
    (b : I → Bool) : Finset (I → Bool) :=
  Finset.univ.filter fun a => boolSupport a ⊂ boolSupport b

theorem boolAvoid_mass_eq_apply_add_lower {I : Type*}
    [Fintype I] [DecidableEq I] (p : PMF (I → Bool)) (b : I → Bool) :
    p.toMeasure (boolAvoid (Finset.univ \ boolSupport b)) =
      p b + ∑ a ∈ boolLower b, p a := by
  rw [PMF.toMeasure_apply_fintype]
  rw [show (∑ x, (boolAvoid (Finset.univ \ boolSupport b)).indicator p x) =
      ∑ x ∈ Finset.univ.filter
        (fun a => boolSupport a ⊆ boolSupport b), p x by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro a ha
    by_cases hsub : boolSupport a ⊆ boolSupport b <;>
      simp [Set.indicator, mem_boolAvoid_compl_support_iff, hsub]
    ]
  rw [show Finset.univ.filter
      (fun a => boolSupport a ⊆ boolSupport b) = insert b (boolLower b) by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, boolLower]
    constructor
    · intro hsub
      by_cases heq : boolSupport a = boolSupport b
      · exact Or.inl (boolSupport_injective heq)
      · exact Or.inr (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, heq⟩)
    · rintro (rfl | hproper)
      · exact Finset.Subset.rfl
      · exact hproper.subset]
  have hb : b ∉ boolLower b := by
    simp only [boolLower, Finset.mem_filter, Finset.mem_univ, true_and]
    intro h
    exact h.2 Finset.Subset.rfl
  rw [Finset.sum_insert hb]

theorem PMF.ext_of_boolAvoid_eq {I : Type*}
    [Fintype I] [DecidableEq I] {p q : PMF (I → Bool)}
    (h : ∀ T : Finset I, p.toMeasure (boolAvoid T) =
      q.toMeasure (boolAvoid T)) :
    p = q := by
  apply PMF.ext
  intro b
  induction n : (boolSupport b).card using Nat.strong_induction_on generalizing b with
  | h n ih =>
      have hmass := h (Finset.univ \ boolSupport b)
      rw [boolAvoid_mass_eq_apply_add_lower,
        boolAvoid_mass_eq_apply_add_lower] at hmass
      have hlower : (∑ a ∈ boolLower b, p a) =
          ∑ a ∈ boolLower b, q a := by
        apply Finset.sum_congr rfl
        intro a ha
        have hproper : boolSupport a ⊂ boolSupport b :=
          (Finset.mem_filter.mp ha).2
        apply ih (boolSupport a).card
          (by simpa [← n] using Finset.card_lt_card hproper) a rfl
      rw [hlower] at hmass
      apply (ENNReal.add_right_inj (ENNReal.sum_ne_top.mpr
        (fun a ha => PMF.apply_ne_top q a))).mp
      simpa [add_comm] using hmass

def currentLocalParity {I : Type*} (a : I → ℕ) : I → Bool :=
  fun i => decide (Odd (a i))

theorem finiteParityKernel_eq_zero_of_ne {E : Type*} [DecidableEq E]
    (S : Finset E) (beta : ℝ) (odd : ↑S → Bool) (a : ↑S → ℕ)
    (hne : odd ≠ currentLocalParity a) :
    finiteParityKernel S beta odd a = 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  unfold finiteParityKernel
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  cases hodd : odd i
  · have hi' : false ≠ decide (Odd (a i)) := by
      simpa [currentLocalParity, hodd] using hi
    have hd : decide (Odd (a i)) = true :=
      Bool.eq_true_of_not_eq_false (Ne.symm hi')
    have hpar : Odd (a i) := of_decide_eq_true hd
    have heven : ¬ Even (a i) := Nat.not_even_iff_odd.mpr hpar
    simp [parityEdgeKernel, heven]
  · have hi' : true ≠ decide (Odd (a i)) := by
      simpa [currentLocalParity, hodd] using hi
    have hd : decide (Odd (a i)) = false :=
      Bool.eq_false_of_not_eq_true (Ne.symm hi')
    have hpar : ¬ Odd (a i) := of_decide_eq_false hd
    simp [parityEdgeKernel, hpar]

theorem finiteParityPMF_eq_zero_of_ne {E : Type*} [DecidableEq E]
    (S : Finset E) (beta : ℝ) (hbeta : 0 < beta)
    (odd : ↑S → Bool) (a : ↑S → ℕ)
    (hne : odd ≠ currentLocalParity a) :
    finiteParityPMF S beta hbeta odd a = 0 := by
  rw [finiteParityPMF_apply,
    finiteParityKernel_eq_zero_of_ne S beta odd a hne]
  simp

theorem bind_finiteParityPMF_apply {E : Type*} [DecidableEq E]
    (S : Finset E) (beta : ℝ) (hbeta : 0 < beta)
    (p : PMF (↑S → Bool)) (a : ↑S → ℕ) :
    p.bind (finiteParityPMF S beta hbeta) a =
      p (currentLocalParity a) *
        finiteParityPMF S beta hbeta (currentLocalParity a) a := by
  rw [PMF.bind_apply, tsum_eq_single (currentLocalParity a)]
  intro odd hodd
  rw [finiteParityPMF_eq_zero_of_ne S beta hbeta odd a hodd]
  simp

end StatMech.FrontierB

