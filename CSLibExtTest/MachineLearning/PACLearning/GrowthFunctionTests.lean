/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.MachineLearning.PACLearning.GrowthFunction
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Card
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Card

/-! # Growth function tests

Thresholds have VC dimension one, closed intervals have VC dimension two,
and the two-constant class has VC dimension at most one.
-/

@[expose] public section

open Cslib.MachineLearning.PACLearning
open scoped Classical

namespace CSLibExtTest.MachineLearning.PACLearning

/-- Threshold concepts on the reals. -/
noncomputable def thresholdClass : ConceptClass ℝ Bool :=
  {c | ∃ a : ℝ, c = fun x => @decide (x < a) (Classical.propDecidable (x < a))}

/-- Closed-interval concepts on the reals. -/
noncomputable def intervalClass : ConceptClass ℝ Bool :=
  {c | ∃ a b : ℝ, c = fun x => @decide (a ≤ x ∧ x ≤ b)
    (Classical.propDecidable (a ≤ x ∧ x ≤ b))}

/-- The two constant concepts. -/
noncomputable def twoConstClass (α : Type*) : ConceptClass α Bool :=
  ↑({fun _ : α => false, fun _ : α => true} : Finset (α → Bool))

/-- Every singleton is shattered by thresholds. -/
theorem threshold_singleton_shattered (a : ℝ) :
    SetShatters thresholdClass {a} := by
  intro W' hW'
  rw [Set.subset_singleton_iff] at hW'
  rcases Classical.em (a ∈ W') with ha | ha
  · refine ⟨fun x => @decide (x < a + 1) (Classical.propDecidable (x < a + 1)),
      ⟨a + 1, rfl⟩, ?_⟩
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
      decide_eq_true_eq]
    constructor
    · rintro ⟨-, rfl⟩
      exact ha
    · intro hx
      rw [hW' x hx]
      exact ⟨lt_add_one a, rfl⟩
  · refine ⟨fun x => @decide (x < a) (Classical.propDecidable (x < a)), ⟨a, rfl⟩, ?_⟩
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
      decide_eq_true_eq]
    constructor
    · rintro ⟨hlt, rfl⟩
      exact absurd hlt (lt_irrefl _)
    · intro hx
      rw [hW' x hx] at hx
      exact absurd hx ha

/-- No ordered pair is shattered by thresholds. -/
private theorem threshold_no_two_ordered (x y : ℝ) (hlt : x < y) :
    ¬ SetShatters thresholdClass ↑({x, y} : Finset ℝ) := by
  intro hshat
  have hsub : ({y} : Set ℝ) ⊆ ↑({x, y} : Finset ℝ) := by
    intro t ht
    rw [Set.mem_singleton_iff.mp ht]
    simp
  obtain ⟨c, ⟨a₀, hcEq⟩, hc⟩ := hshat {y} hsub
  have hyL : y ∈ c ⁻¹' {true} ∩ ↑({x, y} : Finset ℝ) := by
    rw [hc]; exact Set.mem_singleton_iff.mpr rfl
  have hya₀ : y < a₀ := by
    have hcy : c y = true := hyL.1
    simp only [hcEq] at hcy
    exact of_decide_eq_true hcy
  have hxyn : x ∉ ({y} : Set ℝ) := by
    simp only [Set.mem_singleton_iff]
    exact ne_of_lt hlt
  have hxW : x ∈ (↑({x, y} : Finset ℝ) : Set ℝ) := by simp
  have hxL : x ∉ c ⁻¹' {true} ∩ ↑({x, y} : Finset ℝ) := by
    rw [hc]; exact hxyn
  have hnx : ¬ x < a₀ := by
    intro hlt'
    have hcx : c x = true := by
      simp only [hcEq]
      exact decide_eq_true_eq.mpr hlt'
    exact hxL ⟨hcx, hxW⟩
  exact hnx (lt_trans hlt hya₀)

/-- No two-point set is shattered by thresholds. -/
theorem threshold_no_two_shattered (s : Finset ℝ) (hs : s.card = 2) :
    ¬ SetShatters thresholdClass ↑s := by
  obtain ⟨x, y, hne, rfl⟩ := Finset.card_eq_two.mp hs
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact threshold_no_two_ordered x y hlt
  · have hswap : ({x, y} : Finset ℝ) = {y, x} := by
      ext z
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact or_comm
    rw [hswap]
    exact threshold_no_two_ordered y x hlt

/-- Thresholds on the reals have VC dimension one. -/
theorem threshold_vcDim : vcDim thresholdClass = 1 := by
  have hle : ∀ W : Finset ℝ, SetShatters thresholdClass ↑W → W.card ≤ 1 := by
    intro W hW
    by_contra hcon
    have h2 : 2 ≤ W.card := lt_of_not_ge hcon
    obtain ⟨t, htsub, htcard⟩ := Finset.exists_subset_card_eq h2
    exact threshold_no_two_shattered t htcard
      (SetShatters.subset hW (fun x hx => htsub hx))
  have hfin : HasFiniteVCDim thresholdClass := hasFiniteVCDim_iff.mpr ⟨1, hle⟩
  have h1mem : 1 ∈ {n : ℕ | ∃ W : Finset ℝ, W.card = n ∧ SetShatters thresholdClass (↑W)} := by
    refine ⟨{0}, Finset.card_singleton 0, ?_⟩
    rw [Finset.coe_singleton]
    exact threshold_singleton_shattered 0
  apply le_antisymm
  · unfold vcDim
    apply csSup_le'
    rintro n ⟨W, hWcard, hWshat⟩
    rw [← hWcard]
    exact hle W hWshat
  · unfold vcDim
    exact le_csSup hfin h1mem

/-- The pair `{0, 1}` is shattered by closed intervals. -/
theorem interval_pair_shattered : SetShatters intervalClass {0, 1} := by
  intro W' hW'
  have h01 : ∀ y ∈ W', y = 0 ∨ y = 1 := by
    intro y hy
    have hmem := hW' hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    exact hmem
  rcases Classical.em ((0 : ℝ) ∈ W') with h0 | h0
  all_goals rcases Classical.em ((1 : ℝ) ∈ W') with h1 | h1
  · refine ⟨fun x => @decide (0 ≤ x ∧ x ≤ 1) (Classical.propDecidable (0 ≤ x ∧ x ≤ 1)),
      ⟨0, 1, rfl⟩, ?_⟩
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_insert_iff,
      Set.mem_singleton_iff, decide_eq_true_eq]
    constructor
    · rintro ⟨-, rfl | rfl⟩
      · exact h0
      · exact h1
    · intro hx
      rcases h01 x hx with rfl | rfl
      · exact ⟨⟨le_refl 0, zero_le_one⟩, Or.inl rfl⟩
      · exact ⟨⟨zero_le_one, le_refl 1⟩, Or.inr rfl⟩
  · refine ⟨fun x => @decide (0 ≤ x ∧ x ≤ 0) (Classical.propDecidable (0 ≤ x ∧ x ≤ 0)),
      ⟨0, 0, rfl⟩, ?_⟩
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_insert_iff,
      Set.mem_singleton_iff, decide_eq_true_eq]
    constructor
    · rintro ⟨⟨-, hx0⟩, rfl | rfl⟩
      · exact h0
      · exact absurd hx0 (not_le_of_gt zero_lt_one)
    · intro hx
      rcases h01 x hx with rfl | hy1
      · exact ⟨⟨le_refl 0, le_refl 0⟩, Or.inl rfl⟩
      · rw [hy1] at hx
        exact absurd hx h1
  · refine ⟨fun x => @decide (1 ≤ x ∧ x ≤ 1) (Classical.propDecidable (1 ≤ x ∧ x ≤ 1)),
      ⟨1, 1, rfl⟩, ?_⟩
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_insert_iff,
      Set.mem_singleton_iff, decide_eq_true_eq]
    constructor
    · rintro ⟨⟨hx1, -⟩, rfl | rfl⟩
      · exact absurd hx1 (not_le_of_gt zero_lt_one)
      · exact h1
    · intro hx
      rcases h01 x hx with hy0 | rfl
      · rw [hy0] at hx
        exact absurd hx h0
      · exact ⟨⟨le_refl 1, le_refl 1⟩, Or.inr rfl⟩
  · refine ⟨fun x => @decide (2 ≤ x ∧ x ≤ 1) (Classical.propDecidable (2 ≤ x ∧ x ≤ 1)),
      ⟨2, 1, rfl⟩, ?_⟩
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_insert_iff,
      Set.mem_singleton_iff, decide_eq_true_eq]
    constructor
    · rintro ⟨⟨h2x, hx1⟩, -⟩
      exact absurd (le_trans h2x hx1) (not_le_of_gt one_lt_two)
    · intro hx
      rcases h01 x hx with hy0 | hy1
      · rw [hy0] at hx
        exact absurd hx h0
      · rw [hy1] at hx
        exact absurd hx h1

/-- A point strictly between two others blocks shattering by intervals. -/
private theorem interval_middle_false (s : Finset ℝ) (u v w : ℝ)
    (hu : u ∈ s) (hv : v ∈ s) (hw : w ∈ s)
    (huv : u < v) (hvw : v < w) (hshat : SetShatters intervalClass ↑s) : False := by
  have hsub : ({u, w} : Set ℝ) ⊆ ↑s := by
    intro t ht
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl
    · exact hu
    · exact hw
  obtain ⟨c, ⟨a₀, b₀, hcEq⟩, hc⟩ := hshat {u, w} hsub
  have hmemU : u ∈ c ⁻¹' {true} ∩ ↑s := by
    rw [hc]; exact Set.mem_insert_iff.mpr (Or.inl rfl)
  have hmemW : w ∈ c ⁻¹' {true} ∩ ↑s := by
    rw [hc]; exact Set.mem_insert_iff.mpr (Or.inr rfl)
  have hmemV : v ∉ c ⁻¹' {true} ∩ ↑s := by
    rw [hc]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact fun h => h.elim (fun he => ne_of_lt huv he.symm) (fun he => ne_of_lt hvw he)
  have huT : a₀ ≤ u ∧ u ≤ b₀ := by
    have hcu : c u = true := hmemU.1
    simp only [hcEq] at hcu
    exact of_decide_eq_true (inst := Classical.propDecidable _) hcu
  have hwT : a₀ ≤ w ∧ w ≤ b₀ := by
    have hcw : c w = true := hmemW.1
    simp only [hcEq] at hcw
    exact of_decide_eq_true (inst := Classical.propDecidable _) hcw
  have hvF : ¬ (a₀ ≤ v ∧ v ≤ b₀) := by
    intro hab
    have hcv : c v = true := by
      simp only [hcEq]
      exact (@decide_eq_true_eq _ (Classical.propDecidable _)).mpr hab
    exact hmemV ⟨hcv, hv⟩
  obtain ⟨hau, hub⟩ := huT
  obtain ⟨haw, hwb⟩ := hwT
  exact hvF ⟨le_trans hau (le_of_lt huv), le_trans (le_of_lt hvw) hwb⟩

/-- No three-point set is shattered by closed intervals. -/
theorem interval_no_three_shattered (s : Finset ℝ) (hs : s.card = 3) :
    ¬ SetShatters intervalClass ↑s := by
  intro hshat
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp hs
  have hx : x ∈ ({x, y, z} : Finset ℝ) := by simp
  have hy : y ∈ ({x, y, z} : Finset ℝ) := by simp
  have hz : z ∈ ({x, y, z} : Finset ℝ) := by simp
  rcases lt_or_gt_of_ne hxy with hxy | hxy
  · rcases lt_or_gt_of_ne hxz with hxz | hxz
    · rcases lt_or_gt_of_ne hyz with hyz | hyz
      · exact interval_middle_false _ x y z hx hy hz hxy hyz hshat
      · exact interval_middle_false _ x z y hx hz hy hxz hyz hshat
    · rcases lt_or_gt_of_ne hyz with hyz | hyz
      · exact absurd (lt_trans (lt_trans hxz hxy) hyz) (lt_irrefl z)
      · exact interval_middle_false _ z x y hz hx hy hxz hxy hshat
  · rcases lt_or_gt_of_ne hxz with hxz | hxz
    · rcases lt_or_gt_of_ne hyz with hyz | hyz
      · exact interval_middle_false _ y x z hy hx hz hxy hxz hshat
      · exact absurd (lt_trans (lt_trans hyz hxy) hxz) (lt_irrefl z)
    · rcases lt_or_gt_of_ne hyz with hyz | hyz
      · exact interval_middle_false _ y z x hy hz hx hyz hxz hshat
      · exact interval_middle_false _ z y x hz hy hx hyz hxy hshat

/-- Closed intervals on the reals have VC dimension two. -/
theorem interval_vcDim : vcDim intervalClass = 2 := by
  have hle : ∀ W : Finset ℝ, SetShatters intervalClass ↑W → W.card ≤ 2 := by
    intro W hW
    by_contra hcon
    have h3 : 3 ≤ W.card := lt_of_not_ge hcon
    obtain ⟨t, htsub, htcard⟩ := Finset.exists_subset_card_eq h3
    exact interval_no_three_shattered t htcard
      (SetShatters.subset hW (fun x hx => htsub hx))
  have hfin : HasFiniteVCDim intervalClass := hasFiniteVCDim_iff.mpr ⟨2, hle⟩
  have h2mem : 2 ∈ {n : ℕ | ∃ W : Finset ℝ, W.card = n ∧ SetShatters intervalClass (↑W)} := by
    refine ⟨{0, 1}, Finset.card_pair zero_ne_one, ?_⟩
    rw [Finset.coe_insert, Finset.coe_singleton]
    exact interval_pair_shattered
  apply le_antisymm
  · unfold vcDim
    apply csSup_le'
    rintro n ⟨W, hWcard, hWshat⟩
    rw [← hWcard]
    exact hle W hWshat
  · unfold vcDim
    exact le_csSup hfin h2mem

/-- The two-constant class has VC dimension at most one. -/
theorem two_const_vcDim_le_one {α : Type*} [Nonempty α] :
    vcDim (twoConstClass α) ≤ 1 := by
  have hH : ({fun _ : α => false, fun _ : α => true} : Finset (α → Bool)).Nonempty :=
    ⟨fun _ : α => false, by simp⟩
  have hL4 := vcDim_le_log_two_card
    ({fun _ : α => false, fun _ : α => true} : Finset (α → Bool))
    (twoConstClass α) rfl hH
  have hne : (fun _ : α => false) ≠ (fun _ : α => true) := by
    intro h
    obtain ⟨x⟩ := (inferInstance : Nonempty α)
    have hx := congrFun h x
    simp at hx
  have hcard :
      ({fun _ : α => false, fun _ : α => true} : Finset (α → Bool)).card = 2 :=
    Finset.card_pair_eq_two_iff.mpr hne
  rw [hcard] at hL4
  have h' : 2 ^ vcDim (twoConstClass α) ≤ 2 ^ 1 := by simpa using hL4
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h'

/-- The two-constant class realizes both traces on a singleton sample. -/
theorem two_const_growth_one :
    growthFunction (twoConstClass (Fin 1)) 1 = 2 := by
  have hle : growthFunction (twoConstClass (Fin 1)) 1 ≤ 2 := by
    have h := growthFunction_le_two_pow (twoConstClass (Fin 1)) 1
    simpa using h
  have hge : 2 ≤ growthFunction (twoConstClass (Fin 1)) 1 := by
    have hcard : (traceFamily (twoConstClass (Fin 1)) {0}).card = 2 := by
      let x₀ : ({0} : Finset (Fin 1)) :=
        ⟨0, Finset.mem_singleton_self 0⟩
      have huniq : ∀ y : ({0} : Finset (Fin 1)), y = x₀ := by
        intro y
        exact Subtype.ext (Finset.mem_singleton.mp y.property)
      have hfalse_mem :
          (fun _ : Fin 1 => false) ∈ twoConstClass (Fin 1) := by
        unfold twoConstClass
        simp
      have htrue_mem :
          (fun _ : Fin 1 => true) ∈ twoConstClass (Fin 1) := by
        unfold twoConstClass
        simp
      have hmem_empty : (∅ : Finset ({0} : Finset (Fin 1))) ∈
          traceFamily (twoConstClass (Fin 1)) {0} := by
        rw [mem_traceFamily]
        exact ⟨fun _ => false, hfalse_mem, fun x => by simp⟩
      have hmem_univ : (Finset.univ : Finset ({0} : Finset (Fin 1))) ∈
          traceFamily (twoConstClass (Fin 1)) {0} := by
        rw [mem_traceFamily]
        refine ⟨fun _ => true, htrue_mem, fun x => ?_⟩
        simp only [Finset.mem_univ]
      have hclass : ∀ t : Finset ({0} : Finset (Fin 1)),
          t = ∅ ∨ t = Finset.univ := by
        intro t
        by_cases hx : x₀ ∈ t
        · right
          apply Finset.eq_univ_of_forall
          intro y
          rw [huniq y]
          exact hx
        · left
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro y
          rw [huniq y]
          exact hx
      have hne : (∅ : Finset ({0} : Finset (Fin 1))) ≠ Finset.univ := by
        intro h
        have hx : x₀ ∈ Finset.univ := Finset.mem_univ x₀
        rw [← h] at hx
        exact Finset.notMem_empty x₀ hx
      have heq : traceFamily (twoConstClass (Fin 1)) {0} =
          {∅, Finset.univ} := by
        ext t
        constructor
        · intro ht
          rcases hclass t with rfl | rfl
          · simp
          · simp
        · intro ht
          simp only [Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with rfl | rfl
          · exact hmem_empty
          · exact hmem_univ
      rw [heq]
      exact Finset.card_pair hne
    have hle2 :=
      traceFamily_card_le_growthFunction (twoConstClass (Fin 1)) {0}
    rw [Finset.card_singleton] at hle2
    rw [hcard] at hle2
    exact hle2
  exact le_antisymm hle hge

#print axioms Cslib.MachineLearning.PACLearning.traceFamily_card_le_growthFunction
#print axioms Cslib.MachineLearning.PACLearning.growthFunction_le_sum
#print axioms Cslib.MachineLearning.PACLearning.growthFunction_le_exp_pow
#print axioms Cslib.MachineLearning.PACLearning.vcDim_le_log_two_card

end CSLibExtTest.MachineLearning.PACLearning
