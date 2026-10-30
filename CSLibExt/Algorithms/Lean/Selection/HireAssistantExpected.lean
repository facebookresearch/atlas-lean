/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Selection.HireAssistant
public import CSLibExt.Algorithms.Lean.Random.ExpectedCost
public import MathlibExt.Probability.ProbabilityMassFunction.Expectation
public import Mathlib.NumberTheory.Harmonic.Defs

/-!
# Expected number of hires

The expected number of hires made by `hireAssistant` on a uniformly random
permutation of a duplicate-free input is the harmonic number `H_n`
(CLRS, fourth edition, Section 5.2). The proof uses indicator random
variables: the hire count is the sum over positions `i` of the indicator
that position `i` is a strict prefix record, and for each `i` exactly
`1 / (i + 1)` of all permutations have a record at `i`, because among the
first `i + 1` positions each one is equally likely to hold the maximum.

The hires observable is `(hireAssistant ys).time.2`, the second component
of the `TimeM` fee pair, so the expectation is stated directly through
`PMF.expectENN` rather than `expectedTime` (which is for `TimeM Nat`).
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

open scoped ENNReal

variable {α : Type*} [LinearOrder α]

/-- Position `i` of the permuted list `ofFn (fun p => xs.get (σ p))` is a
strict prefix record: every earlier entry is smaller. -/
private abbrev isRecord (xs : List α) (σ : Equiv.Perm (Fin xs.length))
    (i : Fin xs.length) : Prop :=
  ∀ j : Fin xs.length, j.val < i.val → xs.get (σ j) < xs.get (σ i)

private theorem length_filter_eq_sum_map {β : Type*} (q : β → Bool)
    (l : List β) :
    (l.filter q).length = (l.map (fun a => if q a then 1 else 0)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      simp only [List.filter_cons, List.map_cons, List.sum_cons,
        apply_ite List.length, List.length_cons]
      split_ifs <;> omega

private theorem sum_ofFn_nat {n : ℕ} (f : Fin n → ℕ) :
    (List.ofFn f).sum = ∑ i, f i := by
  simp [List.ofFn_eq_map, Finset.sum_eq_multiset_sum]

private theorem map_ofFn_eq {n : ℕ} {β γ : Type*} (g : Fin n → γ)
    (h : γ → β) :
    (List.ofFn g).map h = List.ofFn (fun i => h (g i)) := by
  simp [List.ofFn_eq_map, List.map_map, Function.comp_def]

private theorem zipIdx_ofFn {n : ℕ} {γ : Type*} (f : Fin n → γ) :
    (List.ofFn f).zipIdx = List.ofFn (fun i => (f i, i.val)) := by
  apply List.ext_getElem
  · simp
  · intro i hi1 hi2
    simp [List.getElem_zipIdx]

private theorem all_take_iff_isRecord (xs : List α)
    (σ : Equiv.Perm (Fin xs.length)) (i : Fin xs.length) :
    ((List.ofFn (fun p => xs.get (σ p))).take i.val).all
        (fun a => decide (a < xs.get (σ i))) = true ↔
      isRecord xs σ i := by
  rw [List.all_eq_true]
  constructor
  · intro h j hj
    have hmem : xs.get (σ j) ∈
        (List.ofFn (fun p => xs.get (σ p))).take i.val := by
      rw [List.mem_take_iff_getElem]
      refine ⟨j.val, by simp [hj], by simp⟩
    have hdec := h _ hmem
    simpa using hdec
  · intro h a ha
    rw [List.mem_take_iff_getElem] at ha
    obtain ⟨k, hk, hak⟩ := ha
    have hk1 : k < i.val := lt_of_lt_of_le hk (Nat.min_le_left _ _)
    have hk2 : k < xs.length := by
      have hkm := lt_of_lt_of_le hk (Nat.min_le_right _ _)
      simpa using hkm
    have hlt := h ⟨k, hk2⟩ hk1
    rw [List.getElem_ofFn] at hak
    rw [decide_eq_true_eq, ← hak]
    exact hlt

/-- The number of hires on a permuted input is the sum of the record
indicators over all positions. -/
private theorem hires_eq_sum (xs : List α)
    (σ : Equiv.Perm (Fin xs.length)) :
    (hireAssistant (List.ofFn (fun p => xs.get (σ p)))).time.2 =
      ∑ i : Fin xs.length, if isRecord xs σ i then 1 else 0 := by
  have htime : (hireAssistant
      (List.ofFn (fun p => xs.get (σ p)))).time.2 =
      (hireAssistant (List.ofFn (fun p => xs.get (σ p)))).ret.2.length := by
    rw [hireAssistant_time]
  rw [htime, hireAssistant_hires, List.length_map,
    length_filter_eq_sum_map, zipIdx_ofFn, map_ofFn_eq, sum_ofFn_nat]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : isRecord xs σ i
  · rw [ite_eq_left ((all_take_iff_isRecord xs σ i).mpr h), ite_eq_left h]
  · rw [ite_eq_right (fun hh => h ((all_take_iff_isRecord xs σ i).mp hh)),
      ite_eq_right h]

/-- The permutations whose prefix maximum on positions `≤ i` is attained
at position `j`. -/
private def prefixMaxSet (xs : List α) (i j : Fin xs.length) :
    Finset (Equiv.Perm (Fin xs.length)) :=
  Finset.univ.filter (fun σ => ∀ k : Fin xs.length, k ≤ i → k ≠ j →
    xs.get (σ k) < xs.get (σ j))

private theorem mem_prefixMaxSet {xs : List α} {i j : Fin xs.length}
    {σ : Equiv.Perm (Fin xs.length)} :
    σ ∈ prefixMaxSet xs i j ↔
      ∀ k : Fin xs.length, k ≤ i → k ≠ j →
        xs.get (σ k) < xs.get (σ j) := by
  simp [prefixMaxSet]

private theorem prefixMaxSet_swap (xs : List α)
    (σ : Equiv.Perm (Fin xs.length)) (i j j' : Fin xs.length)
    (hj : j ≤ i) (hj' : j' ≤ i) (h : σ ∈ prefixMaxSet xs i j) :
    σ * Equiv.swap j j' ∈ prefixMaxSet xs i j' := by
  rw [mem_prefixMaxSet] at h ⊢
  intro k hk hkne
  have hk'le : Equiv.swap j j' k ≤ i := by
    by_cases h1 : k = j
    · rw [h1, Equiv.swap_apply_left]; exact hj'
    · by_cases h2 : k = j'
      · rw [h2, Equiv.swap_apply_right]; exact hj
      · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]; exact hk
  have hk'ne : Equiv.swap j j' k ≠ j := by
    intro hEq
    apply hkne
    apply (Equiv.swap j j').injective
    rw [Equiv.swap_apply_right]
    exact hEq
  have hlt := h (Equiv.swap j j' k) hk'le hk'ne
  simpa only [Equiv.Perm.mul_apply, Equiv.swap_apply_right] using hlt

/-- For each position `i`, exactly `n ! / (i + 1)` permutations have a
record at `i`: the `i + 1` prefix-maximum sets partition all permutations
and have equal cardinality by swapping two prefix positions. -/
private theorem card_filter_isRecord (xs : List α) (hxs : xs.Nodup)
    (i : Fin xs.length) :
    (i.val + 1) *
        (Finset.univ.filter (fun σ => isRecord xs σ i)).card =
      (xs.length).factorial := by
  have hAi : prefixMaxSet xs i i =
      Finset.univ.filter (fun σ => isRecord xs σ i) := by
    ext σ
    rw [mem_prefixMaxSet, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    constructor
    · intro h j hj
      have hlt : j < i := hj
      exact h j (le_of_lt hlt) (ne_of_lt hlt)
    · intro h k hk hkne
      have hklt : k < i := lt_of_le_of_ne hk hkne
      exact h k hklt
  have hdisj : ((Finset.Iic i : Set (Fin xs.length))).PairwiseDisjoint
      (prefixMaxSet xs i) := by
    intro j hj j' hj' hne
    have hjle : j ≤ i := Finset.mem_Iic.mp (Finset.mem_coe.mp hj)
    have hj'le : j' ≤ i := Finset.mem_Iic.mp (Finset.mem_coe.mp hj')
    show Disjoint (prefixMaxSet xs i j) (prefixMaxSet xs i j')
    rw [Finset.disjoint_left]
    intro σ hσ hσ'
    rw [mem_prefixMaxSet] at hσ hσ'
    have h1 := hσ j' hj'le (Ne.symm hne)
    have h2 := hσ' j hjle hne
    exact lt_asymm h1 h2
  have hcover : (Finset.Iic i).biUnion (prefixMaxSet xs i) =
      Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro σ
    obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image (Finset.Iic i)
      (fun k => xs.get (σ k)) ⟨i, Finset.mem_Iic.mpr (le_refl i)⟩
    rw [Finset.mem_biUnion]
    refine ⟨j, hj, ?_⟩
    rw [mem_prefixMaxSet]
    intro k hk hkne
    have hle := hmax k (Finset.mem_Iic.mpr hk)
    refine lt_of_le_of_ne hle ?_
    intro hEq
    apply hkne
    apply σ.injective
    exact (List.Nodup.get_inj_iff hxs).mp hEq
  have hcard : ∀ j ∈ Finset.Iic i,
      (prefixMaxSet xs i j).card = (prefixMaxSet xs i i).card := by
    intro j hj
    have hjle : j ≤ i := Finset.mem_Iic.mp hj
    refine Finset.card_bij' (fun σ _ => σ * Equiv.swap j i)
      (fun σ _ => σ * Equiv.swap i j) ?_ ?_ ?_ ?_
    · intro σ hσ
      exact prefixMaxSet_swap xs σ i j i hjle (le_refl i) hσ
    · intro σ hσ
      exact prefixMaxSet_swap xs σ i i j (le_refl i) hjle hσ
    · intro σ _
      rw [Equiv.swap_comm i j, mul_assoc, Equiv.swap_mul_self, mul_one]
    · intro σ _
      rw [Equiv.swap_comm i j, mul_assoc, Equiv.swap_mul_self, mul_one]
  have hsum : (Finset.univ : Finset (Equiv.Perm (Fin xs.length))).card =
      ∑ j ∈ Finset.Iic i, (prefixMaxSet xs i j).card := by
    rw [← hcover, Finset.card_biUnion hdisj]
  rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin] at hsum
  rw [← hAi, hsum, Finset.sum_congr rfl hcard, Finset.sum_const,
    Fin.card_Iic, smul_eq_mul]

/-- The expected number of hires of `hireAssistant` under a uniformly
random permutation of a duplicate-free input is the harmonic sum
`∑ i, 1 / (i + 1)`, valued in `ℝ≥0∞` (CLRS Section 5.2). -/
public theorem hireAssistant_expectedHires (xs : List α) (hxs : xs.Nodup) :
    (uniformPermutation xs).expectENN
        (fun ys => ((hireAssistant ys).time.2 : ℝ≥0∞)) =
      ∑ i : Fin xs.length, ((i.val + 1 : ℝ≥0∞))⁻¹ := by
  have hcast : ∀ σ : Equiv.Perm (Fin xs.length),
      ((hireAssistant (List.ofFn (fun p => xs.get (σ p)))).time.2 :
          ℝ≥0∞) =
        ∑ i, (if isRecord xs σ i then (1 : ℝ≥0∞) else 0) := by
    intro σ
    rw [hires_eq_sum xs σ, Nat.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  have hsum_eq : (∑ σ : Equiv.Perm (Fin xs.length),
      ((hireAssistant (List.ofFn (fun p => xs.get (σ p)))).time.2 :
          ℝ≥0∞)) =
      ∑ σ, ∑ i, (if isRecord xs σ i then (1 : ℝ≥0∞) else 0) :=
    Finset.sum_congr rfl fun σ _ => hcast σ
  have hdist :
      Cslib.Probability.PMF.uniformOfFintype (Equiv.Perm (Fin xs.length)) =
        PMF.uniformFintype (Equiv.Perm (Fin xs.length)) := by
    ext σ
    simp
  rw [uniformPermutation, hdist, PMF.expectENN_map,
    PMF.expectENN_uniformOfFintype, Fintype.card_perm, Fintype.card_fin]
  simp only [Function.comp_apply]
  rw [hsum_eq, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_boole]
  have hcount := card_filter_isRecord xs hxs i
  have hcast' : (i.val + 1 : ℝ≥0∞) *
      ((Finset.univ.filter (fun σ => isRecord xs σ i)).card : ℝ≥0∞) =
      ((xs.length.factorial : ℕ) : ℝ≥0∞) := by
    exact_mod_cast hcount
  have h1 : (((xs.length.factorial : ℕ) : ℝ≥0∞))⁻¹ *
      ((Finset.univ.filter (fun σ => isRecord xs σ i)).card : ℝ≥0∞) *
        (i.val + 1 : ℝ≥0∞) = 1 := by
    have hring : (((xs.length.factorial : ℕ) : ℝ≥0∞))⁻¹ *
        ((Finset.univ.filter (fun σ => isRecord xs σ i)).card : ℝ≥0∞) *
          (i.val + 1 : ℝ≥0∞) =
        (((xs.length.factorial : ℕ) : ℝ≥0∞))⁻¹ *
          ((i.val + 1 : ℝ≥0∞) *
            ((Finset.univ.filter (fun σ => isRecord xs σ i)).card :
              ℝ≥0∞)) := by ring
    rw [hring, hcast', ENNReal.inv_mul_cancel
      (by exact_mod_cast (Nat.factorial_pos _).ne')
      (ENNReal.natCast_ne_top _)]
  exact ENNReal.eq_inv_of_mul_eq_one_left h1

/-- The expected number of hires as a real number is the harmonic sum
`∑ i, 1 / (i + 1)`. -/
public theorem hireAssistant_expectedHires_toReal (xs : List α)
    (hxs : xs.Nodup) :
    ((uniformPermutation xs).expectENN
        (fun ys => ((hireAssistant ys).time.2 : ℝ≥0∞))).toReal =
      ∑ i : Fin xs.length, (1 : ℝ) / (i.val + 1) := by
  rw [hireAssistant_expectedHires xs hxs,
    ENNReal.toReal_sum (fun i _ => by
      exact ENNReal.inv_ne_top.mpr (by positivity))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ENNReal.toReal_inv,
    ENNReal.toReal_add (ENNReal.natCast_ne_top _) ENNReal.one_ne_top,
    ENNReal.toReal_natCast, ENNReal.toReal_one, one_div]

/-- The expected number of hires as a real number is the harmonic number
`H_n`. -/
public theorem hireAssistant_expectedHires_toReal_eq_harmonic
    (xs : List α) (hxs : xs.Nodup) :
    ((uniformPermutation xs).expectENN
        (fun ys => ((hireAssistant ys).time.2 : ℝ≥0∞))).toReal =
      (harmonic xs.length : ℝ) := by
  rw [hireAssistant_expectedHires_toReal xs hxs]
  have hfin : (∑ i : Fin xs.length, (1 : ℝ) / (i.val + 1)) =
      ∑ k ∈ Finset.range xs.length, (1 : ℝ) / (k + 1) :=
    Fin.sum_univ_eq_sum_range (fun k => (1 : ℝ) / (k + 1)) xs.length
  rw [hfin]
  unfold harmonic
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [one_div]

end Cslib.Algorithms.Lean.TimeM
