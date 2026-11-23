/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Open addressing: a counting bound on probe prefixes

Under uniform hashing, the probe sequence of a key in an `m`-slot open-addressing
table is a permutation of the slots, each of the `m!` permutations equally likely.
`first_k_probes_bound` bounds the number of permutations whose first `k` probes all
land in a set `S` of occupied slots by `m! * (|S| / m) ^ k`.
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.OpenAddressing

private theorem step_count {m : ℕ} (S : Finset (Fin m)) (k : ℕ) (hk : k < m) :
    (Finset.univ.filter (fun π : Equiv.Perm (Fin m) => ∀ i : Fin m, (i : ℕ) < k + 1 → π i ∈ S)).card * m ≤
    (Finset.univ.filter (fun π : Equiv.Perm (Fin m) => ∀ i : Fin m, (i : ℕ) < k → π i ∈ S)).card * S.card := by
  classical
  let j : Fin m := ⟨k, hk⟩
  have hjval : (j : ℕ) = k := rfl
  let A := Finset.univ.filter (fun π : Equiv.Perm (Fin m) => ∀ i : Fin m, (i : ℕ) < k + 1 → π i ∈ S)
  let B := Finset.univ.filter (fun π : Equiv.Perm (Fin m) => ∀ i : Fin m, (i : ℕ) < k → π i ∈ S)
  let f : Equiv.Perm (Fin m) × Fin m → Equiv.Perm (Fin m) × Fin m :=
    fun p => (p.1.trans (Equiv.swap (p.1 j) p.2), p.1 j)
  let g : Equiv.Perm (Fin m) × Fin m → Equiv.Perm (Fin m) × Fin m :=
    fun q => (q.1.trans (Equiv.swap q.2 (q.1 j)), q.1 j)
  have hgf : ∀ p : Equiv.Perm (Fin m) × Fin m, g (f p) = p := by
    intro p
    dsimp only [f, g]
    have h1 : (p.1.trans (Equiv.swap (p.1 j) p.2)) j = p.2 := by
      simp [Equiv.swap_apply_left]
    have h2 : (p.1.trans (Equiv.swap (p.1 j) p.2)).trans (Equiv.swap (p.1 j) ((p.1.trans (Equiv.swap (p.1 j) p.2)) j)) = p.1 := by
      rw [h1]
      rw [Equiv.trans_assoc, Equiv.swap_swap, Equiv.trans_refl]
    show ((p.1.trans (Equiv.swap (p.1 j) p.2)).trans (Equiv.swap (p.1 j) ((p.1.trans (Equiv.swap (p.1 j) p.2)) j)), (p.1.trans (Equiv.swap (p.1 j) p.2)) j) = p
    rw [h2, h1]
  have hf_inj : Function.Injective f := by
    have hli : Function.HasLeftInverse f := ⟨g, fun x => hgf x⟩
    exact hli.injective
  have hmaps : Set.MapsTo f ↑(A ×ˢ (Finset.univ : Finset (Fin m))) ↑(B ×ˢ S) := by
    intro p hp
    rw [Finset.mem_coe, Finset.mem_product] at hp
    rw [Finset.mem_coe, Finset.mem_product]
    obtain ⟨hpA, -⟩ := hp
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hpA
    dsimp only [f]
    constructor
    · simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
      intro i hi
      show (Equiv.swap (p.1 j) p.2) (p.1 i) ∈ S
      have hi1 : (i : ℕ) < k + 1 := Nat.lt_add_right 1 hi
      have hpiS : p.1 i ∈ S := hpA i hi1
      have hne : p.1 i ≠ p.1 j := by
        intro hcon
        have hinj := p.1.injective
        have hij : i = j := hinj hcon
        have hval : (i : ℕ) = (j : ℕ) := congrArg (fun x : Fin m => (x : ℕ)) hij
        rw [hjval] at hval
        omega
      by_cases hxb : p.1 i = p.2
      · rw [hxb, Equiv.swap_apply_right]
        have hjS : p.1 j ∈ S := hpA j (by rw [hjval]; omega)
        exact hjS
      · rw [Equiv.swap_apply_of_ne_of_ne hne hxb]
        exact hpiS
    · have hjS : p.1 j ∈ S := hpA j (by rw [hjval]; omega)
      exact hjS
  have hinj : Set.InjOn f ↑(A ×ˢ (Finset.univ : Finset (Fin m))) := hf_inj.injOn
  have hcard := Finset.card_le_card_of_injOn f hmaps hinj
  rw [Finset.card_product, Finset.card_product] at hcard
  rw [Finset.card_univ, Fintype.card_fin] at hcard
  exact hcard

private theorem card_filter_zero {m : ℕ} (S : Finset (Fin m)) :
    (Finset.univ.filter (fun π : Equiv.Perm (Fin m) => ∀ i : Fin m, (i : ℕ) < 0 → π i ∈ S)).card = Nat.factorial m := by
  classical
  have hfil : Finset.univ.filter (fun π : Equiv.Perm (Fin m) => ∀ i : Fin m, (i : ℕ) < 0 → π i ∈ S) = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro π
    rw [Finset.mem_filter]
    constructor
    · exact Finset.mem_univ π
    · intro i hi
      omega
  rw [hfil, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]

private theorem bound_le_aux {m : ℕ} (S : Finset (Fin m)) (hm : 0 < m) (k : ℕ) (hkm : k ≤ m) :
    ((Finset.univ.filter (fun π : Equiv.Perm (Fin m) => ∀ i : Fin m, (i : ℕ) < k → π i ∈ S)).card : ℝ) ≤
    (Nat.factorial m : ℝ) * ((S.card : ℝ) / m) ^ k := by
  classical
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have hratio_nonneg : (0 : ℝ) ≤ (S.card : ℝ) / (m : ℝ) :=
    div_nonneg (Nat.cast_nonneg _) (le_of_lt hm_pos)
  have hall : ∀ k : ℕ, k ≤ m →
      ((Finset.univ.filter (fun π : Equiv.Perm (Fin m) => ∀ i : Fin m, (i : ℕ) < k → π i ∈ S)).card : ℝ) ≤
      (Nat.factorial m : ℝ) * ((S.card : ℝ) / m) ^ k := by
    intro k
    induction k with
    | zero =>
      intro _
      rw [card_filter_zero]
      simp
    | succ k ih =>
      intro hkm
      have hkle : k ≤ m := Nat.le_of_succ_le hkm
      have hklt : k < m := by omega
      have hrec := step_count S k hklt
      have ihk := ih hkle
      have hcast : (((Finset.univ.filter (fun π : Equiv.Perm (Fin m) => ∀ i : Fin m, (i : ℕ) < k + 1 → π i ∈ S)).card : ℕ) : ℝ) * (m : ℝ) ≤
          (((Finset.univ.filter (fun π : Equiv.Perm (Fin m) => ∀ i : Fin m, (i : ℕ) < k → π i ∈ S)).card : ℕ) : ℝ) * (S.card : ℝ) := by
        have hnat : (Finset.univ.filter (fun π : Equiv.Perm (Fin m) => ∀ i : Fin m, (i : ℕ) < k + 1 → π i ∈ S)).card * m ≤
            (Finset.univ.filter (fun π : Equiv.Perm (Fin m) => ∀ i : Fin m, (i : ℕ) < k → π i ∈ S)).card * S.card := hrec
        have hle : ((((Finset.univ.filter (fun π : Equiv.Perm (Fin m) => ∀ i : Fin m, (i : ℕ) < k + 1 → π i ∈ S)).card * m : ℕ)) : ℝ) ≤
            ((((Finset.univ.filter (fun π : Equiv.Perm (Fin m) => ∀ i : Fin m, (i : ℕ) < k → π i ∈ S)).card * S.card : ℕ)) : ℝ) :=
          Nat.cast_le.mpr hnat
        push_cast at hle
        exact hle
      have hdiv : (((Finset.univ.filter (fun π : Equiv.Perm (Fin m) => ∀ i : Fin m, (i : ℕ) < k + 1 → π i ∈ S)).card : ℕ) : ℝ) ≤
          ((((Finset.univ.filter (fun π : Equiv.Perm (Fin m) => ∀ i : Fin m, (i : ℕ) < k → π i ∈ S)).card : ℕ) : ℝ) * (S.card : ℝ)) / (m : ℝ) :=
        (le_div_iff₀ hm_pos).mpr hcast
      have heq : ((((Finset.univ.filter (fun π : Equiv.Perm (Fin m) => ∀ i : Fin m, (i : ℕ) < k → π i ∈ S)).card : ℕ) : ℝ) * (S.card : ℝ)) / (m : ℝ) =
          ((((Finset.univ.filter (fun π : Equiv.Perm (Fin m) => ∀ i : Fin m, (i : ℕ) < k → π i ∈ S)).card : ℕ) : ℝ) * (((S.card : ℝ) / (m : ℝ)))) :=
        mul_div_assoc _ _ _
      rw [heq] at hdiv
      have hstep : (((Finset.univ.filter (fun π : Equiv.Perm (Fin m) => ∀ i : Fin m, (i : ℕ) < k + 1 → π i ∈ S)).card : ℕ) : ℝ) ≤
          ((Nat.factorial m : ℝ) * ((S.card : ℝ) / m) ^ k) * ((S.card : ℝ) / (m : ℝ)) :=
        le_trans hdiv (mul_le_mul_of_nonneg_right ihk hratio_nonneg)
      have hpow : (Nat.factorial m : ℝ) * ((S.card : ℝ) / m) ^ (k + 1) =
          ((Nat.factorial m : ℝ) * ((S.card : ℝ) / m) ^ k) * ((S.card : ℝ) / (m : ℝ)) := by
        rw [pow_succ]
        ring
      rw [hpow]
      exact hstep
  exact hall k hkm

private theorem bound_gt_aux {m : ℕ} (S : Finset (Fin m)) (hm : 0 < m) (k : ℕ) (hkm : m < k) :
    ((Finset.univ.filter (fun π : Equiv.Perm (Fin m) => ∀ i : Fin m, (i : ℕ) < k → π i ∈ S)).card : ℝ) ≤
    (Nat.factorial m : ℝ) * ((S.card : ℝ) / m) ^ k := by
  classical
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have hrhs_nonneg : (0 : ℝ) ≤ (Nat.factorial m : ℝ) * ((S.card : ℝ) / m) ^ k := by
    apply mul_nonneg (Nat.cast_nonneg _)
    apply pow_nonneg
    apply div_nonneg (Nat.cast_nonneg _)
    exact le_of_lt hm_pos
  by_cases hS : S = Finset.univ
  · have hfil : Finset.univ.filter (fun π : Equiv.Perm (Fin m) => ∀ i : Fin m, (i : ℕ) < k → π i ∈ S) = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro π
      rw [Finset.mem_filter]
      constructor
      · exact Finset.mem_univ π
      · intro i _
        rw [hS]
        exact Finset.mem_univ _
    have hcardS : S.card = m := by
      rw [hS, Finset.card_univ, Fintype.card_fin]
    rw [hfil, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
    have hratio : (S.card : ℝ) / (m : ℝ) = 1 := by
      rw [hcardS]
      exact div_self (ne_of_gt hm_pos)
    rw [hratio, one_pow, mul_one]
  · have hsub : S ⊂ Finset.univ := Finset.ssubset_univ_iff.mpr hS
    obtain ⟨j, -, hjS⟩ := Finset.exists_of_ssubset hsub
    have hempty : Finset.univ.filter (fun π : Equiv.Perm (Fin m) => ∀ i : Fin m, (i : ℕ) < k → π i ∈ S) = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro π hmem
      rw [Finset.mem_filter] at hmem
      obtain ⟨-, hpred⟩ := hmem
      have hlt : ((π.symm j : Fin m) : ℕ) < k := by
        have hltm : ((π.symm j : Fin m) : ℕ) < m := Fin.is_lt _
        omega
      have hmemS : π (π.symm j) ∈ S := hpred (π.symm j) hlt
      have happly : π (π.symm j) = j := Equiv.apply_symm_apply π j
      rw [happly] at hmemS
      exact hjS hmemS
    rw [hempty, Finset.card_empty]
    simp only [Nat.cast_zero]
    exact hrhs_nonneg

/-- Open addressing under uniform hashing: a counting bound on probe prefixes.
Slots are `Fin m`, and `S` is the set of occupied slots, of size `n = S.card`.
A probe sequence is a permutation `π` of the slots (`π i` is the `i`-th probed
slot).

For `k ≤ m`, the permutations whose first `k` probes all land in `S` number
exactly `n (n - 1) ⋯ (n - k + 1) * (m - k)!`: the falling factorial `(n)_k` times
the orderings of the remaining `m - k` slots. When `S` is a proper subset of the
slots, an unsuccessful search stops at the first free slot, so these are exactly
the probe sequences on which it makes more than `k` probes. For `k > m`, every
slot is among the first `k` probes, so the count is `m!` when `S` is the whole
table and `0` otherwise; a full table has no free slot.

The theorem states the real-valued upper bound `m! * (n / m) ^ k` on this count,
for every `k`. -/
theorem first_k_probes_bound {m : ℕ} (S : Finset (Fin m))
    (hm : 0 < m) (k : ℕ) :
    ((Finset.univ.filter (fun π : Equiv.Perm (Fin m) =>
      ∀ i : Fin m, (i : ℕ) < k → π i ∈ S)).card : ℝ) ≤
      (Nat.factorial m : ℝ) * ((S.card : ℝ) / m) ^ k := by
  classical
  by_cases hkm : k ≤ m
  · exact bound_le_aux S hm k hkm
  · push Not at hkm
    exact bound_gt_aux S hm k hkm

end Cslib.Algorithms.Lean.OpenAddressing
