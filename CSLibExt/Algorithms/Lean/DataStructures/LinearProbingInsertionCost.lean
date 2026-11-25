/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.LinearProbingAnalysis
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

/-!
# Exact mean insertion cost of linear probing

`insertionCost_eq` gives Knuth's formula for the expected number of probes to insert the
`k`-th item. We use a finite-difference argument. Let `P` sum an observable over the `N`
possible insertions and put `D = P - N • id`. Expanding `P ^ n` by the binomial theorem
expresses the mean after `n` insertions as a sum of terms `choose n j * c j / N ^ j`.

To show that `c j` is independent of `N` for `j < N`, write the probe count as a sum of
indicators that intervals are occupied. Applying `D` to an occupancy indicator marks the
predecessors that an insertion scans and can unmark the cell it fills. Thus each application
adds at most one unmarked position inside the window under consideration. A window that wraps
around the table then requires more occupied cells than the remaining insertions can fill.

The coefficients are determined successively by the case `N = n + 1`. There is one free cell,
so the probe counts from the different addresses are exactly `1, …, N`. Knuth's sum has the same
value on this diagonal by telescoping.
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.LinearProbing

open Finset
open scoped Fin.NatCast

variable {N : ℕ}

private abbrev State (N : ℕ) := Finset (Fin N)
private abbrev Obs (N : ℕ) := State N → ℚ

private def step (N : ℕ) : Module.End ℚ (Obs N) where
  toFun f S := ∑ h : Fin N, f (insert (insertCell S h) S)
  map_add' f g := by ext S; simp [sum_add_distrib]
  map_smul' a f := by ext S; simp [mul_sum]

private def delta (N : ℕ) : Module.End ℚ (Obs N) :=
  step N - algebraMap ℚ _ N

private def coeff (N j : ℕ) : Obs N →ₗ[ℚ] ℚ :=
  (LinearMap.proj (R := ℚ) (φ := fun _ : State N => ℚ) ∅).comp (delta N ^ j)

private lemma delta_apply (f : Obs N) (S : State N) :
    delta N f S = ∑ h : Fin N, (f (insert (insertCell S h) S) - f S) := by
  simp [delta, step, Finset.sum_sub_distrib]

private lemma coeff_succ (j : ℕ) (f : Obs N) :
    coeff N (j + 1) f = coeff N j (delta N f) := by
  simp [coeff, pow_succ]

private lemma delta_support (j : ℕ) (f : Obs N)
    (hf : ∀ S : State N, S.card ≤ j → f S = 0) : coeff N j f = 0 := by
  induction j generalizing f with
  | zero => simpa [coeff] using hf ∅ (by simp)
  | succ j ih =>
    rw [coeff_succ]
    apply ih
    intro S hS
    rw [delta_apply]
    exact sum_eq_zero fun h _ => by
      rw [hf S (by omega), hf _ ((card_insert_le ..).trans (by omega)), sub_zero]

private def marked (T : State N) : Obs N := fun S => if T ⊆ S then 1 else 0

private lemma coeff_marked_zero {j : ℕ} {T : State N} (h : j < T.card) :
    coeff N j (marked T) = 0 := by
  apply delta_support
  intro S hS
  apply ite_eq_right
  exact fun hs => (not_lt_of_ge ((card_le_card hs).trans hS)) h

section Coordinates

variable [NeZero N]

/-- Cell at backward offset `i` from `b`. -/
private def back (b : Fin N) (i : ℕ) : Fin N := b - i

private lemma back_inj (b : Fin N) : Set.InjOn (back b) (↑(range N) : Set ℕ) := by
  intro i hi j hj hij
  simp only [coe_range, Set.mem_Iio] at hi hj
  have eq : (i : Fin N) = j := sub_right_inj.mp hij
  simpa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using congrArg Fin.val eq

private lemma rotate_pow_apply' (h : Fin N) (k : ℕ) :
    (finRotate N ^ k) h = h + (k : Fin N) := by
  induction k with
  | zero => simp
  | succ k ih => simp [pow_succ', Equiv.Perm.mul_apply, ih, add_assoc]

private lemma rotate_back (b : Fin N) (i : ℕ) :
    finRotate N (back b (i + 1)) = back b i := by
  simp [back, sub_add_eq_sub_sub]

private lemma scan_le (S : State N) (b : Fin N) (x : ℕ) (hx : back b x ∉ S)
    (r fuel : ℕ) (hr : r ≤ fuel) :
    displacementAux S (back b (x + r)) fuel ≤ r := by
  induction r generalizing fuel with
  | zero => cases fuel <;> simp [displacementAux, hx]
  | succ r ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      simp only [displacementAux, ← Nat.add_assoc, rotate_back]
      split <;> first | exact Nat.succ_le_succ (ih _ (by omega)) | omega

private lemma scan_eq (S : State N) (b : Fin N) (x r fuel : ℕ) (hr : r ≤ fuel)
    (hx : back b x ∉ S) :
    displacementAux S (back b (x + r)) fuel = r ↔
      ∀ i ∈ Ioc x (x + r), back b i ∈ S := by
  induction r generalizing fuel with
  | zero => cases fuel <;> simp [displacementAux, hx]
  | succ r ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      simp only [displacementAux, ← Nat.add_assoc, rotate_back]
      rw [show Ioc x (x + r + 1) = insert (x + r + 1) (Ioc x (x + r)) by
        ext i; simp; omega]
      by_cases h : back b (x + r + 1) ∈ S <;> simp [h, ih fuel (by omega)]

private lemma target_iff (S : State N) (b : Fin N) (x r : ℕ) (hr : r < N)
    (hx : back b x ∉ S) :
    insertCell S (back b (x + r)) = back b x ↔ ∀ i ∈ Ioc x (x + r), back b i ∈ S := by
  let d := displacement S (back b (x + r))
  have hd : d ≤ r := scan_le S b x hx r N hr.le
  rw [← scan_eq S b x r N hr.le hx]
  change (finRotate N ^ d) (back b (x + r)) = back b x ↔ d = r
  rw [rotate_pow_apply']
  have heq : back b (x + r) + (d : Fin N) = back b x ↔ (d : Fin N) = r := by
    unfold back
    rw [Nat.cast_add, sub_add_eq_sub_sub, add_comm, ← eq_sub_iff_add_eq, sub_sub_self]
  rw [heq]
  constructor
  · intro e
    simpa [Nat.mod_eq_of_lt (lt_of_le_of_lt hd hr), Nat.mod_eq_of_lt hr] using congrArg Fin.val e
  · exact fun e => congrArg Nat.cast e

private def pattern (b : Fin N) (T : Finset ℕ) : Obs N := marked (T.image (back b))

private lemma pattern_apply (b : Fin N) (T : Finset ℕ) (S : State N) :
    pattern b T S = if ∀ i ∈ T, back b i ∈ S then 1 else 0 := by
  simp [pattern, marked, image_subset_iff]

private lemma pattern_insert (b : Fin N) (T : Finset ℕ) (hT : T ⊆ range N)
    (S : State N) (q : Fin N) :
    pattern b T (insert q S) - pattern b T S =
      ∑ x ∈ T, if q = back b x then pattern b (T.erase x) S - pattern b T S else 0 := by
  by_cases hq : ∃ x ∈ T, q = back b x
  · obtain ⟨x, hx, rfl⟩ := hq
    rw [sum_eq_single_of_mem x hx, ite_eq_left rfl]
    · congr 1
      simp only [pattern_apply]
      congr 1
      apply propext
      constructor
      · intro h i hi
        obtain ⟨hne, hi⟩ := mem_erase.mp hi
        exact (mem_insert.mp (h i hi)).resolve_left (fun e => hne (back_inj b (hT hi) (hT hx) e))
      · intro h i hi
        by_cases e : i = x
        · simp [e]
        · exact mem_insert_of_mem (h i (mem_erase.mpr ⟨e, hi⟩))
    · intro i hi hne
      exact ite_eq_right (fun e => hne (back_inj b (hT hi) (hT hx) e.symm))
  · rw [sum_eq_zero (fun i hi => ite_eq_right (fun e => hq ⟨i, hi, e⟩)), sub_eq_zero]
    simp only [pattern_apply]
    congr 1
    apply propext
    exact ⟨fun h i hi => (mem_insert.mp (h i hi)).resolve_left (fun e => hq ⟨i, hi, e.symm⟩),
      fun h i hi => mem_insert_of_mem (h i hi)⟩

private lemma sum_back (b : Fin N) (x : ℕ) (f : Fin N → ℚ) :
    ∑ h, f h = ∑ r ∈ range N, f (back b (x + r)) := by
  rw [← Fin.sum_univ_eq_sum_range]
  simpa [back, sub_add_eq_sub_sub] using ((Equiv.subLeft (b - (x : Fin N))).sum_comp f).symm

/-- To complete a pattern, the insertion must fill a missing cell `x`. A hash address
`r` steps behind `x` reaches it exactly when all `r` intervening cells are occupied.
Subtracting the second indicator enforces that `x` was empty. -/
private lemma delta_pattern (b : Fin N) (T : Finset ℕ) (hT : T ⊆ range N) :
    delta N (pattern b T) = ∑ x ∈ T, ∑ r ∈ range N,
      (pattern b (T.erase x ∪ Ioc x (x + r)) - pattern b (T ∪ Ioc x (x + r))) := by
  ext S
  simp only [delta_apply, pattern_insert b T hT, Finset.sum_apply, Pi.sub_apply]
  rw [sum_comm]
  refine sum_congr rfl fun x hx => ?_
  rw [sum_back b x]
  refine sum_congr rfl fun r hr => ?_
  by_cases hb : back b x ∈ S
  · have he : (∀ i ∈ T.erase x, back b i ∈ S) ↔ ∀ i ∈ T, back b i ∈ S := by
      constructor
      · intro h i hi
        by_cases e : i = x
        · simpa [e] using hb
        · exact h i (mem_erase.mpr ⟨e, hi⟩)
      · exact fun h i hi => h i (mem_of_mem_erase hi)
    simp only [pattern_apply, forall_mem_union]
    split_ifs <;> norm_num <;> tauto
  · simp only [target_iff S b x r (mem_range.mp hr) hb]
    have ht : ¬ ∀ i ∈ T, back b i ∈ S := fun h => hb (h x hx)
    simp only [pattern_apply, forall_mem_union, ht, false_and, ite_false, sub_zero]
    split_ifs <;> first | rfl | tauto

private lemma card_window (b : Fin N) (x r : ℕ) (hr : r ≤ N) :
    ((Ioc x (x + r)).image (back b)).card = r := by
  rw [card_image_of_injOn, Nat.card_Ioc, Nat.add_sub_cancel_left]
  intro i hi k hk e
  simp only [coe_Ioc, Set.mem_Ioc] at hi hk
  have aux (v : ℕ) (hv : x < v) :
      back b v = back (back b (x + 1)) (v - (x + 1)) := by
    simp [back, ← sub_add_eq_sub_sub, ← Nat.cast_add, Nat.add_sub_of_le hv]
  rw [aux i hi.1, aux k hk.1] at e
  have := back_inj (back b (x + 1)) (x₁ := i - (x + 1)) (x₂ := k - (x + 1))
    (mem_range.mpr (by omega)) (mem_range.mpr (by omega)) e
  omega

/-- A scan across more than `j` predecessors has zero coefficient of order `j`. -/
private lemma coeff_pattern_succ (b : Fin N) (T : Finset ℕ) (hT : T ⊆ range N)
    (j : ℕ) (hj : j < N) :
    coeff N (j + 1) (pattern b T) = ∑ x ∈ T, ∑ r ∈ range (j + 1),
      (coeff N j (pattern b (T.erase x ∪ Ioc x (x + r))) -
        coeff N j (pattern b (T ∪ Ioc x (x + r)))) := by
  simp only [coeff_succ, delta_pattern b T hT, map_sum, map_sub]
  refine sum_congr rfl fun x _ => (sum_subset (range_mono hj) ?_).symm
  intro r hr hrj
  have zero (U : Finset ℕ) : coeff N j (pattern b (U ∪ Ioc x (x + r))) = 0 := by
    apply coeff_marked_zero
    have h := card_le_card (image_mono (f := back b) (subset_union_right (s₁ := U)
      (s₂ := Ioc x (x + r))))
    rw [card_window b x r (mem_range.mp hr).le] at h
    simp only [mem_range, not_lt] at hrj
    omega
  simp [zero]

/-- A window with too few unmarked positions cannot be occupied in `j` insertions. -/
private lemma crowded (b : Fin N) {T : Finset ℕ} {j m w : ℕ} (hm : m ≤ N) (hw : m ≤ w)
    (h : (range w \ T).card + j < m) : coeff N j (pattern b T) = 0 := by
  apply coeff_marked_zero
  have hsub : (range m ∩ T).image (back b) ⊆ T.image (back b) :=
    image_mono _ inter_subset_right
  have he := card_image_of_injOn (s := range m ∩ T) ((back_inj b).mono
    (show (↑(range m ∩ T) : Set ℕ) ⊆ ↑(range N) from
      fun _ hi => range_mono hm (mem_inter.mp hi).1))
  have hcard := card_le_card hsub
  rw [he] at hcard
  have hdiff := card_le_card (sdiff_subset_sdiff (range_mono hw) (Subset.refl T))
  have hsum := card_sdiff_add_card_inter (range m) T
  rw [card_range] at hsum
  omega

/-- The centered coefficient of a pattern is independent of the size of the circle once
the missing positions in its window and the number of insertions fit strictly inside it. -/
private lemma coeff_local {M : ℕ} [NeZero M] (b : Fin N) (c : Fin M) (j w : ℕ)
    (T : Finset ℕ) (hT : T ⊆ range w) (h : (range w \ T).card + j < min N M) :
    coeff N j (pattern b T) = coeff M j (pattern c T) := by
  induction j generalizing w T with
  | zero => simp [coeff, pattern, marked]
  | succ j ih =>
    by_cases hw : min N M ≤ w
    · rw [crowded b (min_le_left ..) hw (by omega : (range w \ T).card + (j + 1) < min N M),
        crowded c (min_le_right ..) hw h]
    have hN := min_le_left N M
    have hM := min_le_right N M
    rw [coeff_pattern_succ b T (hT.trans (range_mono (by omega))) j (by omega),
      coeff_pattern_succ c T (hT.trans (range_mono (by omega))) j (by omega)]
    refine sum_congr rfl fun x hx => sum_congr rfl fun r _ => ?_
    let v := max w (x + r + 1)
    have hxw := mem_range.mp (hT hx)
    have hU : T ∪ Ioc x (x + r) ⊆ range v := by
      intro i hi
      rcases mem_union.mp hi with hi | hi
      · exact range_mono (le_max_left ..) (hT hi)
      · have := (mem_Ioc.mp hi).2
        simp only [v, mem_range]; omega
    have hE : T.erase x ∪ Ioc x (x + r) ⊆ T ∪ Ioc x (x + r) :=
      union_subset_union (erase_subset ..) (Subset.refl _)
    have hholes : range v \ (T.erase x ∪ Ioc x (x + r)) ⊆ insert x (range w \ T) := by
      intro i hi
      simp only [v, mem_sdiff, mem_range, mem_union, mem_erase, mem_Ioc] at hi
      simp only [mem_insert, mem_sdiff, mem_range]
      by_cases e : i = x
      · exact Or.inl e
      · exact Or.inr ⟨by omega, fun hit => hi.2 (Or.inl ⟨e, hit⟩)⟩
    have hec := (card_le_card hholes).trans (card_insert_le ..)
    have huc := card_le_card (sdiff_subset_sdiff (Subset.refl (range v)) hE)
    rw [ih v _ (hE.trans hU) (by omega), ih v _ hU (by omega)]

private lemma scan_ge (S : State N) (h : Fin N) (r fuel : ℕ) (hr : r ≤ fuel) :
    r ≤ displacementAux S h fuel ↔ ∀ i < r, h + (i : Fin N) ∈ S := by
  induction r generalizing fuel h with
  | zero => simp
  | succ r ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      rw [Nat.forall_lt_succ_left']
      simp only [displacementAux, finRotate_apply, Nat.cast_zero, add_zero]
      by_cases ht : h ∈ S
      · simp only [ht, ite_true, Nat.succ_le_succ_iff, ih (h + 1) fuel (by omega),
          true_and, Nat.cast_succ]
        simp [add_assoc, add_comm (1 : Fin N)]
      · simp [ht]

private def probeObs (h : Fin N) : Obs N := fun S => probes S h

/-- The empty interval accounts for the first probe, each further probe for an occupied prefix. -/
private lemma probe_pattern (h : Fin N) :
    probeObs h = ∑ r ∈ range (N + 1), pattern (h + ((r - 1 : ℕ) : Fin N)) (range r) := by
  ext S
  let d := displacement S h
  have hd : d ≤ N := by
    have aux (f : ℕ) (g : Fin N) : displacementAux S g f ≤ f := by
      induction f generalizing g with
      | zero => rfl
      | succ f ih =>
        simp only [displacementAux]; split <;> first | exact Nat.succ_le_succ (ih _) | omega
    exact aux N h
  have refl (r : ℕ) (i : ℕ) (hi : i < r) :
      back (h + ((r - 1 : ℕ) : Fin N)) i = h + ((r - 1 - i : ℕ) : Fin N) := by
    have e : (r - 1 - i : ℕ) + i = r - 1 := by omega
    rw [back, sub_eq_iff_eq_add, add_assoc, ← Nat.cast_add, e]
  have he (r : ℕ) (hr : r ∈ range (N + 1)) :
      pattern (h + ((r - 1 : ℕ) : Fin N)) (range r) S = if r ≤ d then 1 else 0 := by
    have hiff := scan_ge S h r N (by simpa using hr)
    have rev : (∀ i ∈ range r, back (h + ((r - 1 : ℕ) : Fin N)) i ∈ S) ↔
        ∀ i < r, h + (i : Fin N) ∈ S := by
      simp only [mem_range]
      constructor
      · intro H i hi
        have hr' : r - 1 - i < r := by omega
        simpa [refl _ _ hr', show r - 1 - (r - 1 - i) = i by omega] using H _ hr'
      · intro H i hi
        rw [refl _ _ hi]
        exact H _ (by omega)
    rw [pattern_apply]
    change _ = if r ≤ displacementAux S h N then 1 else 0
    split_ifs <;> first | rfl | tauto
  change (probes S h : ℚ) = _
  rw [Finset.sum_apply, sum_congr rfl he]
  have hfilter : (range (N + 1)).filter (· ≤ d) = range (d + 1) := by
    ext; simp; omega
  simp [probes, d, hfilter]

private lemma coeff_probe_local {M : ℕ} [NeZero M] (h : Fin N) (g : Fin M)
    (j : ℕ) (hN : j < N) (hM : j < M) : coeff N j (probeObs h) = coeff M j (probeObs g) := by
  have trim {K : ℕ} [NeZero K] (p : Fin K) (hj : j < K) :
      coeff K j (probeObs p) =
        ∑ r ∈ range (j + 1), coeff K j (pattern (p + ((r - 1 : ℕ) : Fin K)) (range r)) := by
    rw [probe_pattern, map_sum]
    refine (sum_subset (range_mono (by omega)) ?_).symm
    intro r hr hrj
    apply coeff_marked_zero
    have hr' : range r ⊆ range K := range_mono (by simpa using hr)
    rw [card_image_of_injOn ((back_inj _).mono hr'), card_range]
    simp only [mem_range, not_lt] at hrj
    omega
  rw [trim h hN, trim g hM]
  refine sum_congr rfl fun r _ => coeff_local _ _ j r _ (Subset.refl _) (by simp [hN, hM])

end Coordinates

private lemma step_pow (n : ℕ) (S : State N) (f : Obs N) :
    (step N ^ n) f S = ∑ a : Fin n → Fin N,
      f ((List.ofFn a).foldl (fun s h => insert (insertCell s h) s) S) := by
  induction n generalizing S with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp, ← (Fin.consEquiv (fun _ : Fin (n + 1) => Fin N)).sum_comp,
      Fintype.sum_prod_type]
    change (∑ h : Fin N, (step N ^ n) f _) = _
    refine sum_congr rfl fun h _ => ?_
    rw [ih]
    congr 1 with a
    simp [Fin.consEquiv]

private lemma expand_step (n : ℕ) (f : Obs N) :
    (step N ^ n) f ∅ = ∑ j ∈ range (n + 1),
      (n.choose j : ℚ) * N ^ (n - j) * coeff N j f := by
  let scalar := algebraMap ℚ (Module.End ℚ (Obs N)) (N : ℚ)
  have hc : Commute (delta N) scalar := (Algebra.commutes (R := ℚ) (N : ℚ) (delta N)).symm
  have eqn : step N = delta N + scalar := by simp [delta, scalar]
  rw [eqn, hc.add_pow, LinearMap.sum_apply, Finset.sum_apply]
  refine sum_congr rfl fun j _ => ?_
  rw [mul_assoc, mul_apply_eq_comp, mul_apply_eq_comp]
  dsimp only [scalar]
  rw [← map_pow, Module.algebraMap_end_apply,
    show (↑(n.choose j) : Module.End ℚ (Obs N)) = algebraMap ℚ _ (n.choose j : ℚ) by simp,
    Module.algebraMap_end_apply]
  simp [coeff, mul_assoc, mul_left_comm]

private def universal (j : ℕ) : ℚ := coeff (j + 1) j (probeObs 0)

private lemma insertion_expansion (N n : ℕ) (hn : n < N) :
    insertionCost N n = ∑ j ∈ range (n + 1), (n.choose j : ℚ) * universal j / N ^ j := by
  have : NeZero N := ⟨by omega⟩
  have nz : (N : ℚ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
  have eqn (h : Fin N) : (∑ a : Fin n → Fin N, (probes (occupancy (List.ofFn a)) h : ℚ)) =
      ∑ j ∈ range (n + 1), n.choose j * (N : ℚ) ^ (n - j) * universal j := by
    change (∑ a : Fin n → Fin N, probeObs h ((List.ofFn a).foldl _ ∅)) = _
    rw [← step_pow, expand_step]
    refine sum_congr rfl fun j hj => ?_
    have hjn : j ≤ n := by simpa using hj
    rw [coeff_probe_local h (0 : Fin (j + 1)) j (hjn.trans_lt hn) (by omega)]
    rfl
  rw [insertionCost, sum_comm]
  simp_rw [eqn]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [mul_sum, sum_div]
  refine sum_congr rfl fun j hj => ?_
  have hjn : j ≤ n := by simpa using hj
  have hp : (N : ℚ) ^ n = N ^ (n - j) * N ^ j := by rw [← pow_add, Nat.sub_add_cancel hjn]
  rw [pow_succ, hp]
  field_simp

/-- With one empty cell the displacements are the distinct backward distances to it. -/
private lemma insertion_diagonal (n : ℕ) :
    insertionCost (n + 1) n = (n + 2 : ℚ) / 2 := by
  have row (a : Fin n → Fin (n + 1)) :
      (∑ h : Fin (n + 1), (probes (occupancy (List.ofFn a)) h : ℚ)) =
        (n + 1 : ℚ) * (n + 2) / 2 := by
    let S := occupancy (List.ofFn a)
    have hcard : S.card = n := by
      simp [S, card_occupancy (by simp : (List.ofFn a).length ≤ n + 1)]
    have hone : Sᶜ.card = 1 := by simp [card_compl, hcard]
    obtain ⟨b, hb⟩ := card_eq_one.mp hone
    have hempty (v : Fin (n + 1)) : v ∉ S ↔ v = b := by
      rw [← mem_compl, hb, mem_singleton]
    have dp (r : ℕ) (hr : r ∈ range (n + 1)) : displacement S (back b r) = r := by
      have hs := scan_eq S b 0 r (n + 1) (mem_range.mp hr).le
        (by simpa [back] using (hempty b).mpr rfl)
      simp only [zero_add] at hs
      apply hs.mpr
      intro i hi
      simp only [mem_Ioc] at hi
      by_contra hn
      have he : back b i = back b 0 := by simpa [back] using (hempty _).mp hn
      have := back_inj b (x₁ := i) (x₂ := 0) (mem_range.mpr (by have := mem_range.mp hr; omega))
        (mem_range.mpr (by omega)) he
      omega
    rw [sum_back b 0]
    change (∑ r ∈ range (n + 1), (probes S (back b (0 + r)) : ℚ)) = _
    simp only [zero_add, probes, Nat.cast_add, Nat.cast_one, sum_add_distrib,
      sum_const, card_range, nsmul_eq_mul, mul_one]
    rw [sum_congr rfl (fun i hi => congrArg (Nat.cast : ℕ → ℚ) (dp i hi))]
    have hsum := congrArg (Nat.cast : ℕ → ℚ) (sum_range_id_mul_two (n + 1))
    simp at hsum
    linarith
  rw [insertionCost]
  simp_rw [row]
  simp [pow_succ]
  field_simp

private def weight (j : ℕ) : ℚ :=
  ((if j = 0 then 1 else 0) + (j + 1) * (j.factorial : ℚ)) / 2

private lemma weight_sum (N n : ℕ) :
    (∑ j ∈ range (n + 1), (n.choose j : ℚ) * weight j / N ^ j) =
      (1 + knuthE 1 N (n + 1)) / 2 := by
  have term (j : ℕ) : (n.choose j : ℚ) * weight j / N ^ j =
      ((if j = 0 then 1 else 0) + (1 + j : ℚ) * n.descFactorial j / N ^ j) / 2 := by
    rw [weight, Nat.descFactorial_eq_factorial_mul_choose]
    push_cast
    by_cases hj : j = 0
    · simp [hj]
    · simp [hj]; ring
  rw [sum_congr rfl (fun j _ => term j), ← sum_div, sum_add_distrib]
  simp [knuthE]

private lemma knuth_diagonal (n : ℕ) : knuthE 1 (n + 1) (n + 1) = n + 1 := by
  let A (j : ℕ) : ℚ := n.descFactorial j / (n + 1 : ℚ) ^ j
  have term (j : ℕ) (hj : j ∈ range (n + 1)) :
      (1 + j : ℚ) * n.descFactorial j / (n + 1 : ℚ) ^ j =
        (n + 1) * (A j - A (j + 1)) := by
    have hjn : j ≤ n := by simpa using hj
    simp only [A, Nat.descFactorial_succ, Nat.cast_mul, Nat.cast_sub hjn, pow_succ]
    field_simp
    ring
  have hzero : A (n + 1) = 0 := by simp [A]
  simp only [knuthE, Nat.add_sub_cancel, Nat.choose_one_right, Nat.cast_add, Nat.cast_one]
  rw [sum_congr rfl term, ← mul_sum, sum_range_sub', hzero]
  simp [A]

/-- The diagonal determines one new coefficient at each table size. -/
private lemma universal_eq (j : ℕ) : universal j = weight j := by
  induction j using Nat.strong_induction_on with
  | ind n ih =>
    have h1 := insertion_expansion (n + 1) n (by omega)
    have h2 := weight_sum (n + 1) n
    rw [insertion_diagonal] at h1
    rw [knuth_diagonal] at h2
    have heq := h1.symm.trans ((show (n + 2 : ℚ) / 2 = (1 + (n + 1)) / 2 by ring).trans h2.symm)
    rw [sum_range_succ, sum_range_succ] at heq
    have head : (∑ j ∈ range n, (n.choose j : ℚ) * universal j / (↑(n + 1) : ℚ) ^ j) =
        ∑ j ∈ range n, n.choose j * weight j / (↑(n + 1) : ℚ) ^ j :=
      sum_congr rfl fun j hj => by rw [ih j (mem_range.mp hj)]
    rw [head] at heq
    have nz : (n + 1 : ℚ) ^ n ≠ 0 := by positivity
    simpa [div_left_inj₀ nz] using heq

/-- **Knuth's exact mean insertion cost for linear probing** (Knuth, *Notes on "open"
addressing*, 1963, Theorem 2). For `1 ≤ k ≤ N`, the expected number of probes to enter the
`k`-th item into a cyclic table of `N` cells by linear probing, all hash addresses independent and
uniform, is `M(N, k) = (1 + E_1(N, k)) / 2`, where
`E_1(N, k) = ∑_{j < k} (j + 1) (k - 1)(k - 2)⋯(k - j) / N ^ j`. -/
theorem insertionCost_eq (N k : ℕ) (hk : 1 ≤ k) (hkN : k ≤ N) :
    insertionCost N (k - 1) = (1 + knuthE 1 N k) / 2 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  rw [Nat.succ_sub_one, insertion_expansion N n (by omega)]
  simp_rw [universal_eq]
  exact weight_sum N n

end Cslib.Algorithms.Lean.LinearProbing
