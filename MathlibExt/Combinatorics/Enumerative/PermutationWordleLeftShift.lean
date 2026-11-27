/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.PermutationWordle
public import MathlibExt.NumberTheory.LucasSequence
import all MathlibExt.Combinatorics.Enumerative.PermutationWordleDerangements
import Mathlib.Data.Fintype.Powerset

/-!
# Three-guess solves for the left-shift strategy

For `n ≥ 4`, the left-shift strategy solves exactly `lucasNumber n - n - 1` secrets on guess three
with the first correct position on guess two. Their missed positions on guess two are
precisely the cyclically nonadjacent subsets of size at least two.
-/

namespace MetaMathlibExt
namespace card_solvedIn_three_firstCorrectAt_two_cyclicShiftLeft

open Finset
open card_derangements_solvedIn_three_cyclicShift (shift shift_mem_ne shift_index
  shift_outside next_index rotate_ne)

variable {n : ℕ}

private def Separated (I : Finset (Fin n)) : Prop :=
  ∀ i ∈ I, finRotate n i ∉ I

-- The second guess is the successor. The third shifts its entries forward on the missed set.
private def third (I : Finset (Fin n)) : Equiv.Perm (Fin n) :=
  (shift I).symm.trans (finRotate n)

private def misses (π : Equiv.Perm (Fin n)) : Finset (Fin n) :=
  univ.filter fun i => finRotate n i ≠ π i

private theorem misses_third (I : Finset (Fin n)) (hI : 2 ≤ I.card) :
    misses (third I) = I := by
  ext i
  simp only [misses, mem_filter, mem_univ, true_and, third, Equiv.trans_apply,
    ne_eq, Equiv.apply_eq_iff_eq, eq_comm (a := i), Equiv.symm_apply_eq]
  by_cases hi : i ∈ I
  · simpa [hi, eq_comm] using (shift_mem_ne I hI hi).2
  · simp [hi, shift_outside I hi]

-- The entry from i lands at its own position exactly when the subset successor is i + 1.
private theorem derangement_iff (hn : 2 ≤ n) (I : Finset (Fin n)) (hI : 2 ≤ I.card) :
    (∀ j, third I j ≠ j) ↔ Separated I := by
  have fixed (i : Fin n) : third I (shift I i) = finRotate n i := by simp [third]
  constructor
  · intro hd i hi hr
    let e := I.orderEmbOfFin rfl
    obtain ⟨a, rfl⟩ : i ∈ Set.range e := I.range_orderEmbOfFin rfl ▸ hi
    obtain ⟨b, hb⟩ : finRotate n (e a) ∈ Set.range e := I.range_orderEmbOfFin rfl ▸ hr
    apply hd (shift I (e a))
    rw [fixed, shift_index, next_index e a b hb.symm]
    exact hb.symm
  · intro hs j hj
    obtain ⟨i, rfl⟩ := (shift I).surjective j
    rw [fixed] at hj
    by_cases hi : i ∈ I
    · exact hs i hi (hj ▸ (shift_mem_ne I hI hi).1)
    · exact rotate_ne hn i (hj.trans (shift_outside I hi))

private theorem second_guess (π : Equiv.Perm (Fin n)) (hπ : ∀ i, π i ≠ i) :
    permWordleGuess (cyclicShiftLeftStrategy n) π 1 = ⇑(finRotate n) := by
  rw [permWordleGuess_one_of_forall_ne _ _ hπ, cyclicShiftLeftStrategy_self, Equiv.symm_symm]

private theorem third_guess (π : Equiv.Perm (Fin n)) (hπ : ∀ i, π i ≠ i)
    (hI : (misses π).card < n) :
    permWordleGuess (cyclicShiftLeftStrategy n) π 2 = ⇑(third (misses π)) := by
  rw [permWordleGuess_succ _ π 1, second_guess _ hπ]
  change permuteAlong (misses π) rfl (cyclicShiftLeftStrategy n _) (finRotate n) = _
  rw [cyclicShiftLeftStrategy_of_ne hI.ne]
  funext i
  by_cases hi : i ∈ misses π
  · simp [third, permuteAlong, shift, hi, Equiv.Perm.extendDomain_symm,
      Equiv.Perm.extendDomain_apply_subtype _ _ hi]
  · simp [third, permuteAlong, shift, hi, Equiv.Perm.extendDomain_symm,
      Equiv.Perm.extendDomain_apply_not_subtype _ _ hi]

private theorem game_iff (hn : 2 ≤ n) (π : Equiv.Perm (Fin n)) :
    (PermWordleSolvedIn (cyclicShiftLeftStrategy n) π 3 ∧
      PermWordleFirstCorrectAt (cyclicShiftLeftStrategy n) π 2) ↔
      (∀ i, π i ≠ i) ∧ (misses π).card < n ∧ 2 ≤ (misses π).card ∧ third (misses π) = π := by
  let S := cyclicShiftLeftStrategy n
  change ((1 ≤ 3 ∧ permWordleGuess S π 2 = ⇑π ∧ ∀ j < 2, permWordleGuess S π j ≠ ⇑π) ∧
    1 ≤ 2 ∧ (∃ k, permWordleGuess S π 1 k = π k) ∧
    ∀ j < 1, ∀ k, permWordleGuess S π j k ≠ π k) ↔ _
  have hcard : (misses π).card < n ↔ ∃ k, finRotate n k = π k := by
    simpa [eq_univ_iff_forall, misses] using (misses π).card_lt_iff_ne_univ
  constructor
  · rintro ⟨⟨_, h₃, hearly⟩, _, ⟨k, hk⟩, h₁⟩
    have hd (i : Fin n) : π i ≠ i := (h₁ 0 (by decide) i).symm
    have h₂ := second_guess π hd
    change permWordleGuess S π 1 = _ at h₂
    have hlt := hcard.mpr ⟨k, (congrFun h₂ k).symm.trans hk⟩
    refine ⟨hd, hlt, ?_, Equiv.coe_inj.mp ((third_guess π hd hlt).symm.trans h₃)⟩
    have hs : misses π = Equiv.Perm.support ((finRotate n).symm * π) := by
      ext i
      simp only [misses, mem_filter, mem_univ, true_and, Equiv.Perm.mem_support,
        Equiv.Perm.mul_apply, ne_eq]
      rw [(finRotate n).symm_apply_eq, eq_comm]
    rw [hs]
    apply Equiv.Perm.two_le_card_support_of_ne_one
    intro he
    apply hearly 1 (by decide)
    rw [h₂]
    funext i
    exact ((finRotate n).symm_apply_eq.mp (Equiv.congr_fun he i)).symm
  · rintro ⟨hd, hlt, hsize, hπ⟩
    have h₂ := second_guess π hd
    change permWordleGuess S π 1 = _ at h₂
    obtain ⟨k, hk⟩ := hcard.mp hlt
    refine ⟨⟨by decide, (third_guess π hd hlt).trans (congrArg DFunLike.coe hπ), ?_⟩,
      by decide, ⟨k, (congrFun h₂ k).trans hk⟩, ?_⟩
    · intro j hj he
      rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
      · exact hd ⟨0, by omega⟩ (congrFun he _).symm
      · obtain ⟨i, hi⟩ := card_pos.mp (show 0 < (misses π).card by omega)
        exact (mem_filter.mp hi).2 (congrFun (h₂.symm.trans he) i)
    · intro j hj i
      obtain rfl : j = 0 := by omega
      exact (hd i).symm

private def missedEquiv (hn : 2 ≤ n) :
    {π : Equiv.Perm (Fin n) // PermWordleSolvedIn (cyclicShiftLeftStrategy n) π 3 ∧
      PermWordleFirstCorrectAt (cyclicShiftLeftStrategy n) π 2} ≃
      {I : Finset (Fin n) // Separated I ∧ 2 ≤ I.card} where
  toFun π := by
    obtain ⟨hd, _, hsize, he⟩ := (game_iff hn π.val).mp π.property
    exact ⟨misses π.val, (derangement_iff hn _ hsize).mp (by rwa [he]), hsize⟩
  invFun I := by
    obtain ⟨hs, hsize⟩ := I.property
    have hlt : I.val.card < n := by
      apply (show I.val.card < n ↔ I.val ≠ univ by simpa using I.val.card_lt_iff_ne_univ).mpr
      intro he
      have h := hs ⟨0, by omega⟩ (he ▸ mem_univ _)
      simp [he] at h
    refine ⟨third I.val, (game_iff hn _).mpr ⟨(derangement_iff hn _ hsize).mpr hs, ?_⟩⟩
    rw [misses_third _ hsize]
    exact ⟨hlt, hsize, rfl⟩
  left_inv π := Subtype.ext ((game_iff hn π.val).mp π.property).2.2.2
  right_inv I := Subtype.ext (misses_third _ I.property.2)

-- Partition a family by membership of x, erasing x in the second class.
private theorem split_card {α : Type*} [DecidableEq α] (x : α) (A B C : Finset (Finset α))
    (hB : ∀ s, s ∈ B ↔ s ∈ A ∧ x ∉ s)
    (hC : ∀ s, s ∈ C ↔ insert x s ∈ A ∧ x ∉ s) : A.card = B.card + C.card := by
  have he : A = B ∪ C.image (insert x) := by
    ext s
    simp only [mem_union, mem_image, hB, hC]
    constructor
    · intro h
      by_cases hx : x ∈ s
      · right
        exact ⟨s.erase x, ⟨(insert_erase hx).symm ▸ h, notMem_erase _ _⟩, insert_erase hx⟩
      · exact Or.inl ⟨h, hx⟩
    · rintro (⟨h, _⟩ | ⟨t, ⟨h, _⟩, rfl⟩) <;> exact h
  have hd : Disjoint B (C.image (insert x)) := by
    rw [disjoint_left]
    intro s hs h
    obtain ⟨t, _, rfl⟩ := mem_image.mp h
    exact ((hB _).mp hs).2 (mem_insert_self _ _)
  rw [he, card_union_of_disjoint hd, card_image_of_injOn]
  exact (insert_injOn_notMem x).mono fun s hs => ((hC s).mp hs).2

private def LinearSep (s : Finset (Fin n)) : Prop :=
  ∀ i ∈ s, ∀ j ∈ s, i.val + 1 ≠ j.val

private noncomputable def paths (n a k : ℕ) : Finset (Finset (Fin n)) := by
  classical
  exact univ.filter fun s => (∀ i ∈ s, a ≤ i.val ∧ i.val < a + k) ∧ LinearSep s

private theorem mem_paths {a k : ℕ} {s : Finset (Fin n)} :
    s ∈ paths n a k ↔ (∀ i ∈ s, a ≤ i.val ∧ i.val < a + k) ∧ LinearSep s := by
  simp [paths]

private theorem linearSep_insert {x : Fin n} {s : Finset (Fin n)} :
    LinearSep (insert x s) ↔ LinearSep s ∧
      (∀ i ∈ s, x.val + 1 ≠ i.val) ∧ (∀ i ∈ s, i.val + 1 ≠ x.val) := by
  simp only [LinearSep, forall_mem_insert]
  grind

-- A path of k positions has F(k + 2) independent subsets. At the last position one
-- may either omit it, or include it and omit its predecessor.
private theorem card_paths (a k : ℕ) (hk : a + k ≤ n) : (paths n a k).card = Nat.fib (k + 2) := by
  induction k using Nat.twoStepInduction with
  | zero =>
    have he : paths n a 0 = {∅} := by
      ext s
      simp [mem_paths, eq_empty_iff_forall_notMem, LinearSep]
      grind
    simp [he]
  | one =>
    let x : Fin n := ⟨a, by omega⟩
    have he : paths n a 1 = ({x} : Finset (Fin n)).powerset := by
      ext s
      simp only [mem_paths, mem_powerset, subset_iff, mem_singleton]
      have hx : x.val = a := rfl
      constructor
      · intro h i hi
        exact Fin.ext (by have := h.1 i hi; omega)
      · intro h
        constructor
        · intro i hi
          simp [h hi, hx]
        · intro i hi j hj
          simp [h hi, h hj]
    rw [he, card_powerset, card_singleton]
    decide
  | more k ih₀ ih₁ =>
    let x : Fin n := ⟨a + k + 1, by omega⟩
    have hx : x.val = a + k + 1 := rfl
    rw [split_card x _ (paths n a (k + 1)) (paths n a k), ih₁ (by omega), ih₀ (by omega)]
    · rw [Nat.fib_add_two (n := k + 2), Nat.add_comm]
    · intro s
      simp only [mem_paths]
      grind [Fin.ext_iff]
    · intro s
      simp only [mem_paths, forall_mem_insert, linearSep_insert]
      grind [Fin.ext_iff]

private theorem separated_iff_linear {k : ℕ} (s : Finset (Fin (k + 1))) :
    Separated s ↔ LinearSep s ∧ (Fin.last k ∈ s → 0 ∉ s) := by
  constructor
  · intro hs
    refine ⟨?_, fun hl => finRotate_last ▸ hs (Fin.last k) hl⟩
    intro i hi j hj he
    have hlast : i ≠ Fin.last k := by
      intro h
      simp [h] at he
      omega
    have hnext : finRotate _ i = j := Fin.ext ((coe_finRotate_of_ne_last hlast).trans he)
    exact hs i hi (hnext ▸ hj)
  · rintro ⟨hlin, hwrap⟩ i hi hr
    by_cases hl : i = Fin.last k
    · subst i
      exact hwrap hi (finRotate_last ▸ hr)
    · exact hlin i hi _ hr (coe_finRotate_of_ne_last hl).symm

private theorem lucas_eq_fib_sum (k : ℕ) :
    lucasNumber (k + 3) = Nat.fib (k + 4) + Nat.fib (k + 2) := by
  induction k using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more k ih₀ ih₁ =>
    change lucasNumber (k + 4) + lucasNumber (k + 3) = Nat.fib (k + 6) + Nat.fib (k + 4)
    rw [ih₁, ih₀]
    conv_rhs => rw [Nat.fib_add_two (n := k + 2), Nat.fib_add_two (n := k + 4)]
    ac_rfl

open Classical in
private theorem card_separated (k : ℕ) :
    (univ.filter (Separated (n := k + 3)) : Finset _).card = lucasNumber (k + 3) := by
  classical
  let x := Fin.last (k + 2)
  have hx : x.val = k + 2 := rfl
  -- If the last vertex is used, both the first and the penultimate vertex are excluded.
  rw [split_card x _ (paths (k + 3) 0 (k + 2)) (paths (k + 3) 1 k),
    card_paths _ _ (by omega), card_paths _ _ (by omega), lucas_eq_fib_sum]
  · intro s
    simp only [mem_paths, mem_filter, mem_univ, true_and, separated_iff_linear]
    grind [Fin.ext_iff]
  · intro s
    simp only [mem_paths, mem_filter, mem_univ, true_and, separated_iff_linear,
      linearSep_insert, mem_insert]
    have hz : (0 : Fin (k + 3)).val = 0 := rfl
    grind [Fin.ext_iff]

private theorem card_large_separated (hn : 4 ≤ n) :
    Nat.card {I : Finset (Fin n) // Separated I ∧ 2 ≤ I.card} = lucasNumber n - n - 1 := by
  classical
  let small := insert ∅ ((univ : Finset (Fin n)).powersetCard 1)
  let allSep := univ.filter (Separated (n := n))
  have hs (I : Finset (Fin n)) : I ∈ small ↔ I.card ≤ 1 := by
    simp only [small, mem_insert, mem_powersetCard_univ, ← card_eq_zero]
    omega
  have hsub : small ⊆ allSep := by
    intro I hI
    rw [mem_filter]
    refine ⟨mem_univ _, fun i hi hr => ?_⟩
    have hpair := card_le_card (insert_subset hi (singleton_subset_iff.mpr hr))
    rw [card_pair (rotate_ne (by omega) i).symm] at hpair
    have := (hs I).mp hI
    omega
  have hsmall : small.card = n + 1 := by
    simp [small, card_insert_of_notMem, mem_powersetCard, card_powersetCard]
  have hall : allSep.card = lucasNumber n := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' (show 3 ≤ n by omega)
    exact card_separated k
  have hmem (I : Finset (Fin n)) :
      I ∈ allSep \ small ↔ Separated I ∧ 2 ≤ I.card := by
    simp [allSep, hs, Nat.lt_iff_add_one_le]
  rw [Nat.card_eq_fintype_card, Fintype.card_of_subtype _ hmem, card_sdiff_of_subset hsub,
    hall, hsmall]
  omega

end card_solvedIn_three_firstCorrectAt_two_cyclicShiftLeft

open card_solvedIn_three_firstCorrectAt_two_cyclicShiftLeft in
/-- **Lucas-number count for the left-shift strategy.** Let $n \ge 4$ and let $\mathrm{CSL}_n$
be the strategy whose component on $n$ positions is the left cyclic shift
$j \mapsto j - 1 \bmod n$ and whose component on $m \ne n$ positions is the cyclic shift
$j \mapsto j + 1 \bmod m$. The number of permutations $\pi$ of $\{0, \dots, n-1\}$ that
$\mathrm{CSL}_n$ guesses in exactly three guesses, with the second guess being the first guess
that has a correct position, is $L_n - n - 1$, where $L_n$ is the $n$-th Lucas number
($L_0 = 2$, $L_1 = 1$, $L_{k+2} = L_{k+1} + L_k$).

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Theorem 15 (`jis-2026-26.1.7-thm-15`). -/
public theorem card_solvedIn_three_firstCorrectAt_two_cyclicShiftLeft (n : ℕ)
    (hn : 4 ≤ n) :
    Nat.card {π : Equiv.Perm (Fin n) //
      PermWordleSolvedIn (cyclicShiftLeftStrategy n) π 3 ∧
        PermWordleFirstCorrectAt (cyclicShiftLeftStrategy n) π 2} = lucasNumber n - n - 1 := by
  exact (Nat.card_congr (missedEquiv (by omega))).trans (card_large_separated hn)

end MetaMathlibExt
