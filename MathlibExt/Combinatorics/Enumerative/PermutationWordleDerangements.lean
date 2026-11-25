/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.PermutationWordle
import Mathlib.Data.Fintype.Powerset

/-!
# Three-guess derangements for permutation Wordle

`card_derangements_solvedIn_three_cyclicShift` counts the derangements solved by the cyclic
shift in exactly three guesses, by classifying the sets of positions missed on guess two.
-/

namespace MetaMathlibExt
namespace card_derangements_solvedIn_three_cyclicShift

open Finset

variable {n m : ℕ}

private theorem rotate_ne (hn : 2 ≤ n) (i : Fin n) : finRotate n i ≠ i := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  simp

private theorem two_step (i : Fin m) (h : finRotate m (finRotate m i) = i) : m ≤ 2 := by
  by_contra! hm
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  have hz : (1 : Fin (k + 3)) + 1 = 0 := by simpa [add_assoc] using h
  have := congrArg Fin.val hz
  simp [Fin.val_add, Nat.mod_eq_of_lt (show 2 < k + 3 by omega)] at this

-- If two consecutive positions belong to an ordered subset, they are consecutive in it too.
private theorem next_index (e : Fin m ↪o Fin n) (a b : Fin m)
    (h : finRotate n (e a) = e b) : finRotate m a = b := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero a.pos.ne'
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (e a).pos.ne'
  by_cases hl : e a = Fin.last n
  · rw [hl, finRotate_last] at h
    have ha : a = Fin.last m := le_antisymm (Fin.le_last _) (e.le_iff_le.mp (hl ▸ Fin.le_last _))
    have hb : b = 0 := le_antisymm (e.le_iff_le.mp (h ▸ Fin.zero_le _)) (Fin.zero_le _)
    rw [ha, hb, finRotate_last]
  · have hv := coe_finRotate_of_ne_last hl
    rw [h] at hv
    have hab : a < b := e.lt_iff_lt.mp (show (e a).val < (e b).val by omega)
    have hal : a ≠ Fin.last m := (hab.trans_le (Fin.le_last _)).ne
    have hr := coe_finRotate_of_ne_last hal
    apply Fin.ext
    by_contra hne
    have hlt : finRotate (m + 1) a < b := by
      simp only [Nat.succ_eq_add_one] at hne
      omega
    have mid₁ := e.strictMono ((lt_finRotate_iff_ne_last a).mpr hal)
    have mid₂ := e.strictMono hlt
    omega

/-- The cyclic successor on the selected positions, extended by the identity. -/
private def shift (I : Finset (Fin n)) : Equiv.Perm (Fin n) :=
  (finRotate I.card).extendDomain (I.orderIsoOfFin rfl).toEquiv

private theorem shift_index (I : Finset (Fin n)) (j : Fin I.card) :
    shift I (I.orderEmbOfFin rfl j) = I.orderEmbOfFin rfl (finRotate I.card j) :=
  Equiv.Perm.extendDomain_apply_image _ _ j

private theorem shift_outside (I : Finset (Fin n)) {i : Fin n} (hi : i ∉ I) :
    shift I i = i :=
  Equiv.Perm.extendDomain_apply_not_subtype _ _ hi

private theorem shift_mem_ne (I : Finset (Fin n)) (hI : 2 ≤ I.card) {i : Fin n} (hi : i ∈ I) :
    shift I i ∈ I ∧ shift I i ≠ i := by
  obtain ⟨j, rfl⟩ := (I.range_orderEmbOfFin rfl ▸ hi : i ∈ Set.range (I.orderEmbOfFin rfl))
  rw [shift_index]
  exact ⟨I.orderEmbOfFin_mem _ _, (I.orderEmbOfFin rfl).injective.ne (rotate_ne hI j)⟩

/-- The third guess against a derangement when the second guess misses precisely `I`. -/
private def candidate (I : Finset (Fin n)) : Equiv.Perm (Fin n) :=
  (shift I).symm.trans (finRotate n).symm

private theorem fixed_iff (I : Finset (Fin n)) (i : Fin n) :
    candidate I i = i ↔ shift I (finRotate n i) = i := by
  change (finRotate n).symm ((shift I).symm i) = i ↔ _
  rw [Equiv.symm_apply_eq, Equiv.symm_apply_eq, eq_comm]

private def adjacentPair (i : Fin n) : Finset (Fin n) := {i, finRotate n i}

private theorem card_adjacentPair (hn : 2 ≤ n) (i : Fin n) : (adjacentPair i).card = 2 :=
  card_pair (rotate_ne hn i).symm

private theorem adjacentPair_injective (hn : 3 ≤ n) :
    Function.Injective (adjacentPair (n := n)) := by
  intro i j he
  have hi : i ∈ adjacentPair j := he ▸ mem_insert_self _ _
  have hj : j ∈ adjacentPair i := he ▸ mem_insert_self _ _
  simp only [adjacentPair, mem_insert, mem_singleton] at hi hj
  rcases hi with h | h
  · exact h
  rcases hj with h' | h'
  · exact h'.symm
  have := two_step i (h' ▸ h.symm)
  omega

-- A third guess has a fixed point precisely when the second guess missed an adjacent pair.
private theorem fixed_iff_adjacentPair (hn : 2 ≤ n) (I : Finset (Fin n)) (hI : 2 ≤ I.card)
    (i : Fin n) : candidate I i = i ↔ I = adjacentPair i := by
  rw [fixed_iff]
  constructor
  · intro h
    have hr : finRotate n i ∈ I := by
      by_contra h'
      exact rotate_ne hn i ((shift_outside I h').symm.trans h)
    have hi : i ∈ I := h ▸ (shift_mem_ne I hI hr).1
    let e := I.orderEmbOfFin rfl
    obtain ⟨a, ha⟩ : i ∈ Set.range e := I.range_orderEmbOfFin rfl ▸ hi
    obtain ⟨b, hb⟩ : finRotate n i ∈ Set.range e := I.range_orderEmbOfFin rfl ▸ hr
    -- The subset successor takes a to b and b back to a, so the subset has size two.
    have hab := next_index e a b (ha ▸ hb.symm)
    have hba : finRotate I.card b = a := e.injective (by
      change I.orderEmbOfFin rfl (finRotate I.card b) = _
      rw [← shift_index]
      exact (congrArg (shift I) hb).trans (h.trans ha.symm))
    have hc := two_step a (hab ▸ hba)
    symm
    apply eq_of_subset_of_card_le (insert_subset hi (singleton_subset_iff.mpr hr))
    exact hc.trans_eq (card_adjacentPair hn i).symm
  · rintro rfl
    have hr : finRotate n i ∈ adjacentPair i := by simp [adjacentPair]
    obtain ⟨hm, hne⟩ := shift_mem_ne _ hI hr
    exact (mem_insert.mp hm).resolve_right (fun h => hne (mem_singleton.mp h))

private def missed (π : Equiv.Perm (Fin n)) : Finset (Fin n) :=
  univ.filter fun i => (finRotate n).symm i ≠ π i

private theorem missed_candidate (I : Finset (Fin n)) (hI : 2 ≤ I.card) :
    missed (candidate I) = I := by
  ext i
  simp only [missed, mem_filter, mem_univ, true_and, candidate, Equiv.trans_apply,
    ne_eq, Equiv.apply_eq_iff_eq, eq_comm (a := i), Equiv.symm_apply_eq]
  by_cases hi : i ∈ I
  · simpa [hi, eq_comm] using (shift_mem_ne I hI hi).2
  · simp [hi, shift_outside I hi]

private theorem third_guess (π : Equiv.Perm (Fin n)) (hπ : ∀ i, π i ≠ i) :
    permWordleGuess cyclicShiftStrategy π 2 = ⇑(candidate (missed π)) := by
  rw [permWordleGuess_succ _ π 1, permWordleGuess_one_of_forall_ne _ _ hπ]
  change permuteAlong (missed π) rfl (finRotate _) (finRotate n).symm = _
  funext i
  by_cases hi : i ∈ missed π
  · simp [candidate, permuteAlong, shift, hi, Equiv.Perm.extendDomain_symm,
      Equiv.Perm.extendDomain_apply_subtype _ _ hi]
  · simp [candidate, permuteAlong, shift, hi, Equiv.Perm.extendDomain_symm,
      Equiv.Perm.extendDomain_apply_not_subtype _ _ hi]

private theorem missed_card_iff (π : Equiv.Perm (Fin n)) :
    2 ≤ (missed π).card ↔ ⇑(finRotate n).symm ≠ ⇑π := by
  have hs : missed π = (finRotate n * π).support := by
    ext i
    simp only [missed, mem_filter, mem_univ, true_and, Equiv.Perm.mem_support,
      Equiv.Perm.mul_apply, ne_eq]
    rw [(finRotate n).symm_apply_eq, eq_comm (a := i)]
  constructor
  · rintro hc he
    obtain rfl := Equiv.coe_inj.mp he
    simp [missed] at hc
  · intro he
    rw [hs]
    apply Equiv.Perm.two_le_card_support_of_ne_one
    intro h
    apply he
    funext i
    apply (finRotate n).symm_apply_eq.mpr
    exact (Equiv.congr_fun h i).symm

private theorem solved_iff (hn : 3 ≤ n) (π : Equiv.Perm (Fin n)) (hπ : ∀ i, π i ≠ i) :
    PermWordleSolvedIn cyclicShiftStrategy π 3 ↔
      candidate (missed π) = π ∧ 2 ≤ (missed π).card := by
  have h₀ : permWordleGuess cyclicShiftStrategy π 0 ≠ ⇑π :=
    fun h => hπ ⟨0, by omega⟩ (congrFun h _).symm
  change (1 ≤ 3 ∧ permWordleGuess cyclicShiftStrategy π 2 = ⇑π ∧
    ∀ j < 2, permWordleGuess cyclicShiftStrategy π j ≠ ⇑π) ↔ _
  rw [third_guess π hπ, Equiv.coe_inj, missed_card_iff]
  have h₁ := permWordleGuess_one_of_forall_ne cyclicShiftStrategy π hπ
  constructor
  · exact fun h => ⟨h.2.1, h₁ ▸ h.2.2 1 (by decide)⟩
  · rintro ⟨h, hne⟩
    refine ⟨by decide, h, fun j hj => ?_⟩
    have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl
    · exact h₀
    · rwa [h₁]

private def admissible (I : Finset (Fin n)) : Prop :=
  2 ≤ I.card ∧ ∀ i, I ≠ adjacentPair i

private def missedEquiv (hn : 3 ≤ n) :
    {π : Equiv.Perm (Fin n) // (∀ i, π i ≠ i) ∧ PermWordleSolvedIn cyclicShiftStrategy π 3} ≃
      {I : Finset (Fin n) // admissible I} where
  toFun π := by
    obtain ⟨hc, hI⟩ := (solved_iff hn π.val π.property.1).mp π.property.2
    refine ⟨missed π.val, hI, fun i h => π.property.1 i ?_⟩
    rw [← hc]
    exact (fixed_iff_adjacentPair (by omega) _ hI i).mpr h
  invFun I := by
    have hπ (i : Fin n) := (fixed_iff_adjacentPair (by omega) I.val I.property.1 i).not.mpr
      (I.property.2 i)
    refine ⟨candidate I.val, hπ, (solved_iff hn _ hπ).mpr ?_⟩
    rw [missed_candidate _ I.property.1]
    exact ⟨rfl, I.property.1⟩
  left_inv π := Subtype.ext ((solved_iff hn _ π.property.1).mp π.property.2).1
  right_inv I := Subtype.ext (missed_candidate _ I.property.1)

private theorem card_admissible (hn : 3 ≤ n) :
    Nat.card {I : Finset (Fin n) // admissible I} = 2 ^ n - (2 * n + 1) := by
  classical
  let small := insert ∅ ((univ : Finset (Fin n)).powersetCard 1)
  let pairs := univ.image (adjacentPair (n := n))
  have hs (I : Finset (Fin n)) : I ∈ small ↔ I.card ≤ 1 := by
    simp only [small, mem_insert, mem_powersetCard_univ, ← card_eq_zero]
    omega
  have hd : Disjoint small pairs := by
    rw [Finset.disjoint_left]
    intro I hI hp
    obtain ⟨i, _, rfl⟩ := mem_image.mp hp
    have h := (hs _).mp hI
    rw [card_adjacentPair (by omega)] at h
    omega
  have hc : small.card = n + 1 := by
    simp [small, card_insert_of_notMem, mem_powersetCard, card_powersetCard]
  have hp : pairs.card = n := by
    simp [pairs, card_image_of_injective _ (adjacentPair_injective hn)]
  have hm (I : Finset (Fin n)) : I ∈ univ \ (small ∪ pairs) ↔ admissible I := by
    simp [admissible, pairs, hs, eq_comm, Nat.lt_iff_add_one_le]
  rw [Nat.card_eq_fintype_card, Fintype.card_of_subtype _ hm, card_sdiff_of_subset (subset_univ _),
    card_union_of_disjoint hd, hc, hp, card_univ, Fintype.card_finset, Fintype.card_fin]
  omega

end card_derangements_solvedIn_three_cyclicShift

open card_derangements_solvedIn_three_cyclicShift in
/-- **Derangements solved in three guesses by cyclic shift.** For $n \ge 3$, exactly
$2^n - (2n + 1)$ derangements $\pi$ of $\{0, \dots, n-1\}$ are guessed by the cyclic shift
strategy in exactly three guesses.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Lemma 9 (`jis-2026-26.1.7-lem-9`). -/
public theorem card_derangements_solvedIn_three_cyclicShift (n : ℕ) (hn : 3 ≤ n) :
    Nat.card {π : Equiv.Perm (Fin n) //
      (∀ k, π k ≠ k) ∧ PermWordleSolvedIn cyclicShiftStrategy π 3} = 2 ^ n - (2 * n + 1) := by
  exact (Nat.card_congr (missedEquiv hn)).trans (card_admissible hn)

end MetaMathlibExt
