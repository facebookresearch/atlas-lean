/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.Avoid2313124
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Sum

/-!
# Permutations avoiding 321 and 4123

For `n ≥ 1`, the permutations of `Fin n` with neither a `321` nor a `4123`
subsequence are counted by the Fibonacci number `F_{2n-1}`. Deletion of the
maximum partitions the count according to its position in the final three slots.

## References

* Juan B. Gil, Felix H. Xu, and William Y. Zhu, *Odd-Indexed Fibonacci Numbers via Pattern-Avoiding
  Permutations*, INTEGERS 25 (2025), Article A79, pp. 1–19, Proposition 1.
* The maximum-insertion equivalence adapts the use of `Equiv.Perm.decomposeFin'Symm`
  to insert the minimum in `MathlibExt.Combinatorics.Enumerative.PartitionDiamondsEulerMahonian`
  (`insertMin` and `value_at_slot`).
-/

set_option autoImplicit false

namespace MathlibExt.Combinatorics.Enumerative.OddFibonacciWanted

open Equiv.Perm

private abbrev IsAvoider {n : ℕ} (σ : Equiv.Perm (Fin n)) : Prop :=
  ¬ HasPattern σ pat321 ∧ ¬ HasPattern σ pat4123

private abbrev Avoiders (n : ℕ) := {σ : Equiv.Perm (Fin n) // IsAvoider σ}

-- Invert to insert a specified value at a specified position, and reverse the values
-- before and after the insertion to switch from inserting zero to inserting the maximum.
private noncomputable def insertMaxEquiv (n : ℕ) :
    Fin (n + 2) × Equiv.Perm (Fin (n + 1)) ≃ Equiv.Perm (Fin (n + 2)) :=
  (Equiv.prodCongr (Equiv.refl _) ((Equiv.equivCongr (Equiv.refl _) Fin.revPerm).trans
    (Equiv.symmEquiv _ _))).trans <| decomposeFin'.symm.trans <|
    (Equiv.symmEquiv _ _).trans (Equiv.equivCongr (Equiv.refl _) Fin.revPerm)

private theorem insertMax_at {n : ℕ} (p : Fin (n + 2)) (τ : Equiv.Perm (Fin (n + 1))) :
    insertMaxEquiv n (p, τ) p = Fin.last (n + 1) := by
  simp [insertMaxEquiv]

private theorem insertMax_other {n : ℕ} (p : Fin (n + 2)) (τ : Equiv.Perm (Fin (n + 1)))
    (i : Fin (n + 1)) : insertMaxEquiv n (p, τ) (p.succAbove i) = (τ i).castSucc := by
  have h := decomposeFin'Symm_symm_succAbove p (τ.trans Fin.revPerm).symm (Fin.rev (τ i))
  simpa [insertMaxEquiv, Equiv.symmEquiv, Fin.rev_succ] using congrArg Fin.rev h

-- Any occurrence using the new maximum must start with it. A suffix of length at
-- least three either has a descent (giving 321) or supplies a witness of 4123.
private theorem avoids_insertMax_iff {n : ℕ} (p : Fin (n + 2))
    (τ : Equiv.Perm (Fin (n + 1))) :
    IsAvoider (insertMaxEquiv n (p, τ)) ↔
      IsAvoider τ ∧ n + 1 ≤ p.val + 2 ∧
        ∀ i j : Fin (n + 1), p.val ≤ i.val → i < j → τ i < τ j := by
  simp only [IsAvoider, hasPattern_pat321_iff, hasPattern_pat4123_iff]
  let σ := insertMaxEquiv n (p, τ)
  have hmax : σ p = Fin.last (n + 1) := insertMax_at p τ
  have hval (i) : σ (p.succAbove i) = (τ i).castSucc := insertMax_other p τ i
  have hlt {i j : Fin (n + 1)} : σ (p.succAbove i) < σ (p.succAbove j) ↔ τ i < τ j := by
    rw [hval, hval, Fin.castSucc_lt_castSucc_iff]
  have hne {i j : Fin (n + 2)} (h : σ i < σ j) : i ≠ p := by
    rintro rfl
    rw [hmax] at h
    exact (not_lt_of_ge (Fin.le_last _)) h
  constructor
  · rintro ⟨h321, h4123⟩
    have hsuffix (i j : Fin (n + 1)) (hi : p.val ≤ i.val) (hij : i < j) : τ i < τ j := by
      refine lt_of_not_ge fun hji => h321 ⟨p, p.succAbove i, p.succAbove j,
        (Fin.lt_succAbove_iff_le_castSucc ..).2 hi, Fin.succAbove_lt_succAbove_iff.2 hij, ?_, ?_⟩
      · exact hlt.2 (lt_of_le_of_ne hji (fun h => hij.ne (τ.injective h.symm)))
      · rw [hval, hmax]
        exact Fin.castSucc_lt_last _
    refine ⟨⟨?_, ?_⟩, ?_, hsuffix⟩
    · rintro ⟨a, b, c, hab, hbc, hcb, hba⟩
      exact h321 ⟨p.succAbove a, p.succAbove b, p.succAbove c,
        Fin.succAbove_lt_succAbove_iff.2 hab, Fin.succAbove_lt_succAbove_iff.2 hbc,
        hlt.2 hcb, hlt.2 hba⟩
    · rintro ⟨a, b, c, d, hab, hbc, hcd, hbc', hcd', hda⟩
      exact h4123 ⟨p.succAbove a, p.succAbove b, p.succAbove c, p.succAbove d,
        Fin.succAbove_lt_succAbove_iff.2 hab, Fin.succAbove_lt_succAbove_iff.2 hbc,
        Fin.succAbove_lt_succAbove_iff.2 hcd, hlt.2 hbc', hlt.2 hcd', hlt.2 hda⟩
    · by_contra! h
      let i : Fin (n + 1) := ⟨p.val, by omega⟩
      let j : Fin (n + 1) := ⟨p.val + 1, by omega⟩
      let k : Fin (n + 1) := ⟨p.val + 2, h⟩
      have hij : i < j := by simp [i, j, Fin.lt_def]
      have hjk : j < k := by simp [j, k, Fin.lt_def]
      exact h4123 ⟨p, p.succAbove i, p.succAbove j, p.succAbove k,
        (Fin.lt_succAbove_iff_le_castSucc ..).2 le_rfl, Fin.succAbove_lt_succAbove_iff.2 hij,
        Fin.succAbove_lt_succAbove_iff.2 hjk, hlt.2 (hsuffix i j le_rfl hij),
        hlt.2 (hsuffix j k (Nat.le_succ _) hjk), by rw [hval, hmax]; exact Fin.castSucc_lt_last _⟩
  · rintro ⟨⟨h321, h4123⟩, hsize, hsuffix⟩
    constructor
    · rintro ⟨a, b, c, hab, hbc, hcb, hba⟩
      obtain ⟨b, rfl⟩ := Fin.exists_succAbove_eq (hne hba)
      obtain ⟨c, rfl⟩ := Fin.exists_succAbove_eq (hne hcb)
      have hbc := Fin.succAbove_lt_succAbove_iff.1 hbc
      by_cases ha : a = p
      · exact (hlt.1 hcb).not_gt (hsuffix b c
          ((Fin.lt_succAbove_iff_le_castSucc ..).1 (ha ▸ hab)) hbc)
      · obtain ⟨a, rfl⟩ := Fin.exists_succAbove_eq ha
        exact h321 ⟨a, b, c, Fin.succAbove_lt_succAbove_iff.1 hab, hbc, hlt.1 hcb, hlt.1 hba⟩
    · rintro ⟨a, b, c, d, hab, hbc, hcd, hbc', hcd', hda⟩
      obtain ⟨b, rfl⟩ := Fin.exists_succAbove_eq (hne hbc')
      obtain ⟨c, rfl⟩ := Fin.exists_succAbove_eq (hne hcd')
      obtain ⟨d, rfl⟩ := Fin.exists_succAbove_eq (hne hda)
      have hbc := Fin.succAbove_lt_succAbove_iff.1 hbc
      have hcd := Fin.succAbove_lt_succAbove_iff.1 hcd
      by_cases ha : a = p
      · have hb := (Fin.lt_succAbove_iff_le_castSucc ..).1 (ha ▸ hab)
        have hd := d.is_lt
        simp only [Fin.lt_def] at hbc hcd
        omega
      · obtain ⟨a, rfl⟩ := Fin.exists_succAbove_eq ha
        exact h4123 ⟨a, b, c, d, Fin.succAbove_lt_succAbove_iff.1 hab, hbc, hcd,
          hlt.1 hbc', hlt.1 hcd', hlt.1 hda⟩

private abbrev SlotFiber {n : ℕ} (p : Fin (n + 2)) :=
  {τ : Equiv.Perm (Fin (n + 1)) // IsAvoider (insertMaxEquiv n (p, τ))}

private abbrev AscendingEnd {n : ℕ} (τ : Equiv.Perm (Fin (n + 2))) : Prop :=
  τ (Fin.last n).castSucc < τ (Fin.last (n + 1))

private theorem card_avoiders_eq_sum_slots (n : ℕ) :
    Nat.card (Avoiders (n + 2)) = ∑ p : Fin (n + 2), Nat.card (SlotFiber p) := by
  rw [← Nat.card_sigma]
  exact Nat.card_congr <|
    ((Equiv.subtypeProdEquivSigmaSubtype
      fun p τ => IsAvoider (insertMaxEquiv n (p, τ))).symm.trans
      (insertMaxEquiv n).subtypeEquivOfSubtype).symm

private theorem card_slot_of_early {n : ℕ} (p : Fin (n + 2)) (hp : p.val + 2 < n + 1) :
    Nat.card (SlotFiber p) = 0 :=
  Nat.card_eq_zero.2 <| Or.inl ⟨fun τ => hp.not_ge ((avoids_insertMax_iff p τ.val).1 τ.2).2.1⟩

private theorem card_slot_of_final_two {n : ℕ} (p : Fin (n + 2)) (hp : n ≤ p.val) :
    Nat.card (SlotFiber p) = Nat.card (Avoiders (n + 1)) := by
  apply Nat.card_congr (Equiv.subtypeEquivRight fun τ => ?_)
  rw [avoids_insertMax_iff]
  refine and_iff_left ⟨by omega, fun i j hi hij => ?_⟩
  have hj := j.is_lt
  have hij' := Fin.lt_def.mp hij
  omega

private theorem card_slot_third_last (n : ℕ) :
    Nat.card (SlotFiber (Fin.last n).castSucc.castSucc) =
      Nat.card {τ : Avoiders (n + 2) // AscendingEnd τ.val} := by
  rw [Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (p := IsAvoider) AscendingEnd)]
  apply Nat.card_congr (Equiv.subtypeEquivRight fun τ => ?_)
  rw [avoids_insertMax_iff]
  simp only [Fin.val_castSucc, Fin.val_last, le_refl, true_and, and_congr_right_iff]
  intro _
  constructor
  · intro h
    exact h _ _ (by simp) (by simp [Fin.lt_def])
  · intro h i j hi hij
    have hj := j.is_lt
    simp only [Fin.lt_def] at hij
    have hi' : i = (Fin.last n).castSucc := Fin.ext (by simp; omega)
    have hj' : j = Fin.last (n + 1) := Fin.ext (by simp; omega)
    simpa only [hi', hj'] using h

-- A final descent in an avoider forces the maximum into the penultimate slot.
private theorem not_ascendingEnd_iff {n : ℕ} (σ : Avoiders (n + 2)) :
    ¬ AscendingEnd σ.val ↔ σ.val (Fin.last n).castSucc = Fin.last (n + 1) := by
  let p := σ.val.symm (Fin.last (n + 1))
  have hp : σ.val p = Fin.last (n + 1) := σ.val.apply_symm_apply _
  change ¬ σ.val (Fin.last n).castSucc < σ.val (Fin.last (n + 1)) ↔ _
  constructor
  · intro h
    have hd : σ.val (Fin.last (n + 1)) < σ.val (Fin.last n).castSucc :=
      lt_of_le_of_ne (le_of_not_gt h) (fun he => (Fin.castSucc_lt_last (Fin.last n)).ne
        (σ.val.injective he.symm))
    rcases lt_trichotomy p (Fin.last n).castSucc with hlt | heq | hgt
    · exact (σ.2.1 ((hasPattern_pat321_iff _).2 ⟨p, (Fin.last n).castSucc, Fin.last (n + 1),
        hlt, Fin.castSucc_lt_last _, hd, lt_of_le_of_ne (hp ▸ Fin.le_last _)
          (fun he => hlt.ne (σ.val.injective he.symm))⟩)).elim
    · simpa only [heq] using hp
    · have hp' : p = Fin.last (n + 1) := Fin.ext (by
        have h := p.is_lt
        simp only [Fin.lt_def, Fin.val_last, Fin.val_castSucc] at hgt ⊢
        omega)
      rw [← hp', hp] at hd
      exact ((not_lt_of_ge (Fin.le_last _)) hd).elim
  · intro hp' h
    rw [hp'] at h
    exact (not_lt_of_ge (Fin.le_last _)) h

private theorem card_descending_end (n : ℕ) :
    Nat.card {σ : Avoiders (n + 2) // ¬ AscendingEnd σ.val} = Nat.card (Avoiders (n + 1)) := by
  let p := (Fin.last n).castSucc
  rw [← card_slot_of_final_two p (by simp [p])]
  symm
  apply Nat.card_congr
  refine Equiv.ofBijective (fun τ : SlotFiber p =>
    ⟨⟨insertMaxEquiv n (p, τ.val), τ.2⟩, (not_ascendingEnd_iff _).2 (insertMax_at p τ.val)⟩) ?_
  constructor
  · intro τ₁ τ₂ h
    apply Subtype.ext
    exact congrArg Prod.snd ((insertMaxEquiv n).injective (congrArg (fun σ => σ.val.val) h))
  · intro σ
    obtain ⟨⟨q, τ⟩, h⟩ := (insertMaxEquiv n).surjective σ.val.val
    have hq : q = p := σ.val.val.injective (by
      calc
        σ.val.val q = Fin.last (n + 1) := h ▸ insertMax_at q τ
        _ = σ.val.val p := ((not_ascendingEnd_iff σ.val).1 σ.2).symm)
    subst q
    exact ⟨⟨τ, h ▸ σ.val.2⟩, Subtype.ext (Subtype.ext h)⟩

private theorem card_avoiders_recurrence (n : ℕ) :
    Nat.card (Avoiders (n + 3)) + Nat.card (Avoiders (n + 1)) =
      3 * Nat.card (Avoiders (n + 2)) := by
  classical
  rw [card_avoiders_eq_sum_slots (n + 1)]
  simp only [Fin.sum_univ_castSucc, card_slot_of_final_two (Fin.last (n + 2)) (by simp),
    card_slot_of_final_two (Fin.last (n + 1)).castSucc (by simp), card_slot_third_last]
  have hzero : ∑ i : Fin n, Nat.card (SlotFiber i.castSucc.castSucc.castSucc) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact card_slot_of_early _ (Nat.add_lt_add_right i.is_lt 2)
  rw [hzero]
  simp only [show n + 1 + 1 = n + 2 from rfl, zero_add]
  have hsplit := Nat.card_congr (Equiv.sumCompl (fun τ : Avoiders (n + 2) => AscendingEnd τ.val))
  rw [Nat.card_sum, card_descending_end] at hsplit
  omega

private theorem card_avoiders_small (n : ℕ) (hn : n < 3) : Nat.card (Avoiders n) = n.factorial := by
  have avoids {k : ℕ} (hk : n < k) (σ : Equiv.Perm (Fin n)) (π : Fin k → Fin k) :
      ¬ HasPattern σ π := by
    rw [hasPattern_iff_exists_orderEmbedding]
    rintro ⟨e, -⟩
    have h := Nat.card_le_card_of_injective e e.injective
    simp only [Nat.card_fin] at h
    omega
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv fun σ => ⟨avoids hn σ _, avoids (by omega) σ _⟩),
    Nat.card_perm, Nat.card_fin]

private theorem card_avoiders_fib (n : ℕ) : Nat.card (Avoiders (n + 1)) = Nat.fib (2 * n + 1) := by
  induction n using Nat.twoStepInduction with
  | zero => rw [card_avoiders_small 1 (by decide)]; decide
  | one => rw [card_avoiders_small 2 (by decide)]; decide
  | more n h₁ h₂ =>
    have e₂ : 2 * (n + 1) + 1 = 2 * n + 3 := by omega
    have e₃ : 2 * (n + 2) + 1 = 2 * n + 5 := by omega
    rw [e₂] at h₂
    change Nat.card (Avoiders (n + 2)) = Nat.fib (2 * n + 3) at h₂
    change Nat.card (Avoiders (n + 3)) = Nat.fib (2 * (n + 2) + 1)
    rw [e₃]
    have hr := card_avoiders_recurrence n
    rw [h₁, h₂] at hr
    have hf₂ : Nat.fib (2 * n + 3) = Nat.fib (2 * n + 1) + Nat.fib (2 * n + 2) :=
      Nat.fib_add_two
    have hf₃ : Nat.fib (2 * n + 4) = Nat.fib (2 * n + 2) + Nat.fib (2 * n + 3) :=
      Nat.fib_add_two
    have hf₄ : Nat.fib (2 * n + 5) = Nat.fib (2 * n + 3) + Nat.fib (2 * n + 4) :=
      Nat.fib_add_two
    omega

/-- **$(321, 4123)$-avoiding permutations are counted by odd-indexed Fibonacci numbers.** For
every $n \ge 1$, the number of permutations of $\{0, 1, \dots, n-1\}$ that avoid both patterns
$321$ and $4123$, that is, contain neither of them, is the Fibonacci number $F_{2n-1}$, where
$F_0 = 0$ and $F_1 = 1$.

Source: Juan B. Gil, Felix H. Xu, and William Y. Zhu,
"Odd-Indexed Fibonacci Numbers via Pattern-Avoiding
Permutations", Proposition 1. -/
public theorem card_avoid_321_4123 (n : ℕ) (hn : 1 ≤ n) :
    Nat.card {σ : Equiv.Perm (Fin n) //
      ¬ HasPattern σ pat321 ∧ ¬ HasPattern σ pat4123} =
      Nat.fib (2 * n - 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simpa only [show 2 * (m + 1) - 1 = 2 * m + 1 by omega] using card_avoiders_fib m

end MathlibExt.Combinatorics.Enumerative.OddFibonacciWanted
