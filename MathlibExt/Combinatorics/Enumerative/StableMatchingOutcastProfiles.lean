/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Factorial.Basic
public import MathlibExt.Combinatorics.Enumerative.StableMatchingSequences
import Mathlib.Data.Fintype.Perm
import Mathlib.GroupTheory.Perm.Fin

/-!
# Counting stable-matching profiles with outcasts

For a fixed outcast pair, the two outcasts have unrestricted preference lists. Each other
participant has a prescribed last choice. With three or more participants on each side the
outcast pair is unique; with two on each side we count directly using the four last choices.
-/

set_option autoImplicit false

namespace MetaMathlibExt.StableMatchingSequences

open Nat

private abbrev Rows (n : ℕ) := Fin n → Equiv.Perm (Fin n)

private abbrev LastRows {n : ℕ} (i j : Fin (n + 1)) :=
  {M : Rows (n + 1) // ∀ k, k ≠ i → M k (Fin.last n) = j}

private abbrev OutcastAt {n : ℕ} (P : PreferenceProfile (n + 1))
    (ij : Fin (n + 1) × Fin (n + 1)) : Prop :=
  (∀ k, k ≠ ij.1 → P.1 k (Fin.last n) = ij.2) ∧
    (∀ k, k ≠ ij.2 → P.2 k (Fin.last n) = ij.1)

private abbrev OutcastProfiles (n : ℕ) :=
  {P : PreferenceProfile (n + 1) // ∃ ij, OutcastAt P ij}

private theorem rank_last_iff {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) (j : Fin (n + 1)) :
    (σ.symm j : ℕ) = (n + 1) - 1 ↔ σ (Fin.last n) = j := by
  change (σ.symm j : ℕ) = (Fin.last n : ℕ) ↔ _
  rw [← Fin.ext_iff, Equiv.symm_apply_eq, eq_comm]

-- Swap the last position with zero, then record its image and the remaining permutation.
private def lastDecompose (n : ℕ) :
    Equiv.Perm (Fin (n + 1)) ≃ Fin (n + 1) × Equiv.Perm (Fin n) :=
  (Equiv.equivCongr (Equiv.swap 0 (Fin.last n)) (Equiv.refl _)).trans Equiv.Perm.decomposeFin

private theorem lastDecompose_fst {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) :
    (lastDecompose n σ).1 = σ (Fin.last n) := by
  have h := Equiv.Perm.decomposeFin_symm_apply_zero
    (lastDecompose n σ).1 (lastDecompose n σ).2
  change Equiv.Perm.decomposeFin.symm (lastDecompose n σ) 0 = _ at h
  simpa [lastDecompose, Equiv.equivCongr] using h.symm

private def lastPermEquiv {n : ℕ} (j : Fin (n + 1)) :
    {σ : Equiv.Perm (Fin (n + 1)) // σ (Fin.last n) = j} ≃ Equiv.Perm (Fin n) where
  toFun σ := (lastDecompose n σ.1).2
  invFun σ := ⟨(lastDecompose n).symm (j, σ), by
    rw [← lastDecompose_fst, Equiv.apply_symm_apply]⟩
  left_inv σ := by
    apply Subtype.ext
    apply (lastDecompose n).injective
    rw [Equiv.apply_symm_apply]
    exact Prod.ext (σ.2.symm.trans (lastDecompose_fst σ.1).symm) rfl
  right_inv σ := by simp

private def lastRowsEquiv {n : ℕ} (i j : Fin (n + 1)) :
    LastRows i j ≃ Equiv.Perm (Fin (n + 1)) × (Fin n → Equiv.Perm (Fin n)) :=
  let e := (Fin.insertNthEquiv (fun _ => Equiv.Perm (Fin (n + 1))) i).symm
  let split : LastRows i j ≃ Equiv.Perm (Fin (n + 1)) ×
      {f : Fin n → Equiv.Perm (Fin (n + 1)) // ∀ k, f k (Fin.last n) = j} :=
    (e.subtypeEquiv (fun M => by
      rw [Fin.forall_iff_succAbove i]
      simp [e, Fin.insertNthEquiv_symm_apply, Fin.removeNth, Fin.succAbove_ne])).trans
      (Equiv.subtypeProdEquivProd.trans
        (Equiv.prodCongr (Equiv.subtypeUnivEquiv (fun _ => trivial)) (Equiv.refl _)))
  split.trans (Equiv.prodCongr (Equiv.refl _)
    (Equiv.subtypePiEquivPi.trans (Equiv.piCongrRight fun _ => lastPermEquiv j)))

private theorem lastRows_card {n : ℕ} (i j : Fin (n + 1)) :
    Nat.card (LastRows i j) = (n + 1)! * (n ! ) ^ n := by
  rw [Nat.card_congr (lastRowsEquiv i j), Nat.card_prod, Nat.card_fun]
  simp [Nat.card_eq_fintype_card, Fintype.card_perm]

private def fixedOutcastEquiv {n : ℕ} (ij : Fin (n + 1) × Fin (n + 1)) :
    {P : PreferenceProfile (n + 1) // OutcastAt P ij} ≃
      LastRows ij.1 ij.2 × LastRows ij.2 ij.1 where
  toFun P := (⟨P.1.1, P.2.1⟩, ⟨P.1.2, P.2.2⟩)
  invFun f := ⟨(f.1.1, f.2.1), f.1.2, f.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem exists_other {n : ℕ} (hn : 2 < n) (a b : Fin n) :
    ∃ c : Fin n, c ≠ a ∧ c ≠ b := by
  have h : 1 < (Finset.univ.erase a).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨c, hc, hcb⟩ := Finset.exists_mem_ne h b
  exact ⟨c, (Finset.mem_erase.mp hc).1, hcb⟩

private theorem outcastAt_unique {n : ℕ} (hn : 2 < n + 1) {P : PreferenceProfile (n + 1)}
    {a b : Fin (n + 1) × Fin (n + 1)} (ha : OutcastAt P a) (hb : OutcastAt P b) : a = b := by
  obtain ⟨i, hia, hib⟩ := exists_other hn a.1 b.1
  obtain ⟨j, hja, hjb⟩ := exists_other hn a.2 b.2
  exact Prod.ext ((ha.2 j hja).symm.trans (hb.2 j hjb)) ((ha.1 i hia).symm.trans (hb.1 i hib))

private theorem outcastProfiles_card_succ (n : ℕ)
    (uniquePair : ∀ (P : PreferenceProfile (n + 1)) a b, OutcastAt P a → OutcastAt P b → a = b) :
    Nat.card (OutcastProfiles n) = (n + 1) ^ 4 * (n ! ) ^ (2 * (n + 1)) := by
  let f : (Σ ij : Fin (n + 1) × Fin (n + 1), {P : PreferenceProfile (n + 1) // OutcastAt P ij}) →
      OutcastProfiles n := fun ⟨ij, P⟩ => ⟨P.1, ij, P.2⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨a, P, ha⟩ ⟨b, Q, hb⟩ heq
      have hPQ : P = Q := congrArg Subtype.val heq
      subst Q
      have hab := uniquePair P a b ha hb
      subst b
      rfl
    · rintro ⟨P, ij, h⟩
      exact ⟨⟨ij, P, h⟩, rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_sigma]
  simp only [fun ij => Nat.card_congr (fixedOutcastEquiv ij), Nat.card_prod, lastRows_card,
    Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
  rw [Nat.factorial_succ, Nat.mul_add 2 n 1, Nat.mul_one, pow_add,
    show (4 : ℕ) = 2 + 2 by decide, pow_add, Nat.mul_comm 2 n, pow_mul]
  simp only [Nat.cast_id, pow_two]
  ac_rfl

private abbrev LastChoices := (Fin 2 → Fin 2) × (Fin 2 → Fin 2)

private def choicesHaveOutcasts (P : LastChoices) : Prop :=
  ∃ i j : Fin 2, (∀ k, k ≠ i → P.1 k = j) ∧ (∀ k, k ≠ j → P.2 k = i)

private instance (P : LastChoices) : Decidable (choicesHaveOutcasts P) := by
  unfold choicesHaveOutcasts
  infer_instance

private theorem outcastProfiles_card_two : Nat.card (OutcastProfiles 1) = 14 := by
  -- For two entries, knowing the last entry determines the whole permutation.
  let e := (lastDecompose 1).trans (Equiv.prodUnique (Fin 2) (Equiv.Perm (Fin 1)))
  have he (σ : Equiv.Perm (Fin 2)) : e σ = σ (Fin.last 1) := lastDecompose_fst σ
  let E : PreferenceProfile 2 ≃ LastChoices :=
    Equiv.prodCongr (Equiv.piCongrRight fun _ => e) (Equiv.piCongrRight fun _ => e)
  have hE (P : PreferenceProfile 2) : (∃ ij, OutcastAt P ij) ↔ choicesHaveOutcasts (E P) := by
    rw [Prod.exists]
    unfold choicesHaveOutcasts OutcastAt
    change (∃ i j, (∀ k, k ≠ i → P.1 k (Fin.last 1) = j) ∧
      (∀ k, k ≠ j → P.2 k (Fin.last 1) = i)) ↔
      ∃ i j, (∀ k, k ≠ i → e (P.1 k) = j) ∧ (∀ k, k ≠ j → e (P.2 k) = i)
    simp only [he]
  rw [Nat.card_congr (E.subtypeEquiv hE), Nat.card_eq_fintype_card]
  decide

/-- **Profiles with a pair of outcasts.** In a preference profile for $n$ men and $n$ women, a man
$i$ and a woman $j$ form a pair of outcasts when every man other than $i$ ranks $j$ last and every
woman other than $j$ ranks $i$ last. The number of preference profiles with at least one pair of
outcasts is $14$ if $n = 2$ and $n^4 ((n-1)!)^{2n}$ if $n \ne 2$ (this is $0$ for $n = 0$).

Source: Borodin et al., *Sequences of the Stable Matching Problem*, Journal of
Integer Sequences 27 (2024), Article 24.2.2, Proposition 14
(`jis-2024-24.2.2-prop-14`). -/
public theorem outcast_profiles_card (n : ℕ) :
    Nat.card {P : PreferenceProfile n // ∃ i j : Fin n,
        (∀ i' : Fin n, i' ≠ i → manRank P i' j = n - 1) ∧
          (∀ j' : Fin n, j' ≠ j → womanRank P j' i = n - 1)} =
      if n = 2 then 14 else n ^ 4 * ((n - 1)!) ^ (2 * n) := by
  cases n with
  | zero =>
    let : IsEmpty {P : PreferenceProfile 0 // ∃ i j : Fin 0,
        (∀ i' : Fin 0, i' ≠ i → manRank P i' j = 0 - 1) ∧
          (∀ j' : Fin 0, j' ≠ j → womanRank P j' i = 0 - 1)} :=
      ⟨fun P => P.2.elim fun i _ => i.elim0⟩
    simp
  | succ n =>
    rw [Nat.card_congr (Equiv.subtypeEquivRight (q := fun P => ∃ ij, OutcastAt P ij) (fun P => by
      simp only [manRank, womanRank, rank_last_iff, Prod.exists]))]
    by_cases h : n + 1 = 2
    · have hn : n = 1 := by omega
      subst n
      exact outcastProfiles_card_two
    · rw [ite_eq_right h, Nat.add_sub_cancel]
      apply outcastProfiles_card_succ
      intro P a b ha hb
      by_cases hn : n = 0
      · subst n
        exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
      · exact outcastAt_unique (by omega) ha hb

end MetaMathlibExt.StableMatchingSequences
