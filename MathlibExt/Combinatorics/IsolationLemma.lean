/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Rat.Star
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring

@[expose] public section

open scoped BigOperators

namespace MetaMathlibExt

private def wgt {n : ℕ} (w : Fin n → Fin (2 * n)) (S : Finset (Fin n)) : ℕ :=
  ∑ i ∈ S, ((w i).val + 1)

private noncomputable def amb {n : ℕ} (F : Finset (Finset (Fin n))) (i : Fin n) :
    Finset (Fin n → Fin (2 * n)) := by
  classical
  exact Finset.univ.filter (fun w =>
    ∃ c : ℕ, (∃ S ∈ F, i ∈ S ∧ wgt w S = c) ∧ (∃ S ∈ F, i ∉ S ∧ wgt w S = c) ∧
      (∀ S ∈ F, i ∈ S → c ≤ wgt w S) ∧ (∀ S ∈ F, i ∉ S → c ≤ wgt w S))

private lemma argmin_nonempty {n : ℕ} (F : Finset (Finset (Fin n))) (hF : F.Nonempty)
    (w : Fin n → Fin (2 * n)) :
    (F.filter (fun S => ∀ T ∈ F, wgt w S ≤ wgt w T)).Nonempty := by
  have hs : (F.image (wgt w)).Nonempty := hF.image _
  obtain ⟨S0, hS0, hS0m⟩ := Finset.mem_image.mp (Finset.min'_mem _ hs)
  refine ⟨S0, Finset.mem_filter.mpr ⟨hS0, fun T hT => ?_⟩⟩
  rw [hS0m]
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨T, hT, rfl⟩)

private lemma total_card {n : ℕ} :
    Fintype.card (Fin n → Fin (2 * n)) = (2 * n) ^ n := by
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

private lemma wgt_update_not_mem {n : ℕ} (w : Fin n → Fin (2 * n)) (i : Fin n)
    (a : Fin (2 * n)) (S : Finset (Fin n)) (h : i ∉ S) :
    wgt (Function.update w i a) S = wgt w S := by
  unfold wgt
  apply Finset.sum_congr rfl
  intro j hj
  have hji : j ≠ i := by
    intro h'
    subst h'
    exact h hj
  rw [Function.update_of_ne hji]

private lemma wgt_update_mem {n : ℕ} (w : Fin n → Fin (2 * n)) (i : Fin n)
    (a : Fin (2 * n)) (S : Finset (Fin n)) (h : i ∈ S) :
    wgt (Function.update w i a) S
      = (a.val + 1) + ∑ j ∈ S.erase i, ((w j).val + 1) := by
  unfold wgt
  conv_lhs => rw [← Finset.add_sum_erase _ _ h]
  rw [Function.update_self]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  rw [Function.update_of_ne hji]

private lemma bad_sub_union {n : ℕ} (F : Finset (Finset (Fin n))) (hF : F.Nonempty) :
    Finset.univ.filter (fun w : Fin n → Fin (2 * n) =>
      (F.filter (fun S => ∀ T ∈ F, wgt w S ≤ wgt w T)).card ≠ 1)
      ⊆ Finset.univ.biUnion (fun i => amb F i) := by
  intro w hw
  rw [Finset.mem_filter] at hw
  obtain ⟨-, hne⟩ := hw
  have hnonempty := argmin_nonempty F hF w
  have hpos : 0 < (F.filter (fun S => ∀ T ∈ F, wgt w S ≤ wgt w T)).card :=
    Finset.card_pos.mpr hnonempty
  have h2 : 1 < (F.filter (fun S => ∀ T ∈ F, wgt w S ≤ wgt w T)).card := by omega
  obtain ⟨S, hSmem, T, hTmem, hST⟩ := Finset.one_lt_card.mp h2
  rw [Finset.mem_filter] at hSmem hTmem
  obtain ⟨hSF, hSmin⟩ := hSmem
  obtain ⟨hTF, hTmin⟩ := hTmem
  by_cases hsub : S ⊆ T
  · have hnot : ¬ T ⊆ S := fun h => hST (le_antisymm hsub h)
    rw [← Finset.sdiff_eq_empty_iff_subset] at hnot
    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hnot
    rw [Finset.mem_sdiff] at hi
    rw [Finset.mem_biUnion]
    refine ⟨i, Finset.mem_univ i, ?_⟩
    simp only [amb, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨wgt w T, ⟨T, hTF, hi.1, rfl⟩,
      ⟨S, hSF, hi.2, le_antisymm (hSmin T hTF) (hTmin S hSF)⟩,
      fun U hUF _ => hTmin U hUF, fun U hUF _ => hTmin U hUF⟩
  · rw [← Finset.sdiff_eq_empty_iff_subset] at hsub
    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hsub
    rw [Finset.mem_sdiff] at hi
    rw [Finset.mem_biUnion]
    refine ⟨i, Finset.mem_univ i, ?_⟩
    simp only [amb, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨wgt w S, ⟨S, hSF, hi.1, rfl⟩,
      ⟨T, hTF, hi.2, le_antisymm (hTmin S hSF) (hSmin T hTF)⟩,
      fun U hUF _ => hSmin U hUF, fun U hUF _ => hSmin U hUF⟩

private lemma fiber_uniq {n : ℕ} (F : Finset (Finset (Fin n))) (i : Fin n)
    (w : Fin n → Fin (2 * n)) (a b : Fin (2 * n))
    (ha : Function.update w i a ∈ amb F i)
    (hb : Function.update w i b ∈ amb F i) : a = b := by
  simp only [amb, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  obtain ⟨c, ⟨S1, hS1F, hS1i, hS1c⟩, ⟨T1, hT1F, hT1ni, hT1c⟩, hlow1, hlow1'⟩ := ha
  obtain ⟨c', ⟨S2, hS2F, hS2i, hS2c⟩, ⟨T2, hT2F, hT2ni, hT2c⟩, hlow2, hlow2'⟩ := hb
  have eT2 : wgt (Function.update w i a) T2 = wgt (Function.update w i b) T2 := by
    rw [wgt_update_not_mem _ _ _ _ hT2ni, wgt_update_not_mem _ _ _ _ hT2ni]
  have eT1 : wgt (Function.update w i a) T1 = wgt (Function.update w i b) T1 := by
    rw [wgt_update_not_mem _ _ _ _ hT1ni, wgt_update_not_mem _ _ _ _ hT1ni]
  have hcc1 : c ≤ c' := by
    calc c ≤ wgt (Function.update w i a) T2 := hlow1' T2 hT2F hT2ni
      _ = wgt (Function.update w i b) T2 := eT2
      _ = c' := hT2c
  have hcc2 : c' ≤ c := by
    calc c' ≤ wgt (Function.update w i b) T1 := hlow2' T1 hT1F hT1ni
      _ = wgt (Function.update w i a) T1 := eT1.symm
      _ = c := hT1c
  have hcc : c = c' := le_antisymm hcc1 hcc2
  have eS1 : wgt (Function.update w i a) S1
      = (a.val + 1) + ∑ j ∈ S1.erase i, ((w j).val + 1) :=
    wgt_update_mem _ _ _ _ hS1i
  have eS1' : wgt (Function.update w i b) S1
      = (b.val + 1) + ∑ j ∈ S1.erase i, ((w j).val + 1) :=
    wgt_update_mem _ _ _ _ hS1i
  have eS2 : wgt (Function.update w i a) S2
      = (a.val + 1) + ∑ j ∈ S2.erase i, ((w j).val + 1) :=
    wgt_update_mem _ _ _ _ hS2i
  have eS2' : wgt (Function.update w i b) S2
      = (b.val + 1) + ∑ j ∈ S2.erase i, ((w j).val + 1) :=
    wgt_update_mem _ _ _ _ hS2i
  have key1 : (a.val + 1) + ∑ j ∈ S1.erase i, ((w j).val + 1)
      ≤ (b.val + 1) + ∑ j ∈ S1.erase i, ((w j).val + 1) := by
    rw [← eS1, ← eS1', hS1c]
    calc c = c' := hcc
      _ ≤ wgt (Function.update w i b) S1 := hlow2 S1 hS1F hS1i
  have key2 : (b.val + 1) + ∑ j ∈ S2.erase i, ((w j).val + 1)
      ≤ (a.val + 1) + ∑ j ∈ S2.erase i, ((w j).val + 1) := by
    rw [← eS2', ← eS2, hS2c]
    calc c' = c := hcc.symm
      _ ≤ wgt (Function.update w i a) S2 := hlow1 S2 hS2F hS2i
  have hab1 : a.val ≤ b.val := by
    have h := Nat.le_of_add_le_add_right key1
    omega
  have hab2 : b.val ≤ a.val := by
    have h := Nat.le_of_add_le_add_right key2
    omega
  apply Fin.ext
  omega

private lemma amb_card_le {n : ℕ} (hn : 0 < n) (F : Finset (Finset (Fin n))) (i : Fin n) :
    (amb F i).card ≤ (2 * n) ^ (n - 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hn)
  have hexp : m.succ - 1 = m := by omega
  have hr : Set.InjOn (fun w : Fin (m.succ) → Fin (2 * m.succ) => w ∘ Fin.succAbove i)
      (amb F i) := by
    intro u hu v hv huv
    have huv' : (u ∘ Fin.succAbove i) = (v ∘ Fin.succAbove i) := huv
    have agree : ∀ j : Fin (m.succ), j ≠ i → u j = v j := by
      intro j hj
      obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
      exact congrFun huv' k
    have hvv : v = Function.update u i (v i) := by
      funext j
      by_cases hj : j = i
      · subst hj
        rw [Function.update_self]
      · rw [Function.update_of_ne hj]
        exact (agree j hj).symm
    have hu' : Function.update u i (u i) ∈ amb F i := by
      rw [Function.update_eq_self]
      exact hu
    have hv' : Function.update u i (v i) ∈ amb F i := by
      rw [← hvv]
      exact hv
    have hval : u i = v i := fiber_uniq F i u (u i) (v i) hu' hv'
    funext j
    by_cases hj : j = i
    · subst hj
      exact hval
    · exact agree j hj
  have hle := Finset.card_le_univ
    ((amb F i).image (fun w : Fin (m.succ) → Fin (2 * m.succ) => w ∘ Fin.succAbove i))
  rw [Finset.card_image_of_injOn hr] at hle
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at hle
  rw [hexp]
  exact hle

private lemma isolation_core {n : ℕ} (hn : 0 < n)
    (F : Finset (Finset (Fin n))) (hF : F.Nonempty) :
    (((Finset.univ.filter (fun w : Fin n → Fin (2 * n) =>
      (F.filter (fun S => ∀ T ∈ F, wgt w S ≤ wgt w T)).card = 1)).card : ℚ)
      / (Fintype.card (Fin n → Fin (2 * n)) : ℚ)) ≥ 1 / 2 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hn)
  have hpart : (Finset.univ.filter (fun w : Fin (m.succ) → Fin (2 * m.succ) =>
      (F.filter (fun S => ∀ T ∈ F, wgt w S ≤ wgt w T)).card = 1)).card +
      {a ∈ (Finset.univ : Finset (Fin (m.succ) → Fin (2 * m.succ))) |
        ¬ (F.filter (fun S => ∀ T ∈ F, wgt a S ≤ wgt a T)).card = 1}.card
      = Fintype.card (Fin (m.succ) → Fin (2 * m.succ)) := by
    have h := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun w : Fin (m.succ) → Fin (2 * m.succ) =>
        (F.filter (fun S => ∀ T ∈ F, wgt w S ≤ wgt w T)).card = 1)
    rwa [Finset.card_univ] at h
  have hfeq : (Finset.univ.filter (fun w : Fin (m.succ) → Fin (2 * m.succ) =>
      ¬ (F.filter (fun S => ∀ T ∈ F, wgt w S ≤ wgt w T)).card = 1))
      = (Finset.univ.filter (fun w : Fin (m.succ) → Fin (2 * m.succ) =>
      (F.filter (fun S => ∀ T ∈ F, wgt w S ≤ wgt w T)).card ≠ 1)) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq]
  have hBle : (Finset.univ.filter (fun w : Fin (m.succ) → Fin (2 * m.succ) =>
      ¬ (F.filter (fun S => ∀ T ∈ F, wgt w S ≤ wgt w T)).card = 1)).card
      ≤ (m.succ) * (2 * m.succ) ^ m := by
    have hsub2 : (Finset.univ.filter (fun w : Fin (m.succ) → Fin (2 * m.succ) =>
        ¬ (F.filter (fun S => ∀ T ∈ F, wgt w S ≤ wgt w T)).card = 1))
        ⊆ Finset.univ.biUnion (fun i => amb F i) := by
      rw [hfeq]
      exact bad_sub_union F hF
    have hexp : m.succ - 1 = m := by omega
    have per : ∀ i ∈ (Finset.univ : Finset (Fin (m.succ))),
        (amb F i).card ≤ (2 * m.succ) ^ m := by
      intro i _
      have h := amb_card_le (Nat.succ_pos m) F i
      rwa [hexp] at h
    calc _ ≤ (Finset.univ.biUnion (fun i => amb F i)).card :=
            Finset.card_le_card hsub2
      _ ≤ ∑ i ∈ Finset.univ, (amb F i).card := Finset.card_biUnion_le
      _ ≤ ∑ _ ∈ (Finset.univ : Finset (Fin (m.succ))), (2 * m.succ) ^ m :=
            Finset.sum_le_sum per
      _ = (m.succ) * (2 * m.succ) ^ m := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hJK : Fintype.card (Fin (m.succ) → Fin (2 * m.succ))
      = 2 * ((m.succ) * (2 * m.succ) ^ m) := by
    rw [total_card, Nat.succ_eq_add_one, pow_succ]
    ring
  have hM : (m.succ) * (2 * m.succ) ^ m + (Finset.univ.filter
      (fun w : Fin (m.succ) → Fin (2 * m.succ) =>
        ¬ (F.filter (fun S => ∀ T ∈ F, wgt w S ≤ wgt w T)).card = 1)).card
      ≤ Fintype.card (Fin (m.succ) → Fin (2 * m.succ)) := by
    have h2 : (m.succ) * (2 * m.succ) ^ m + (Finset.univ.filter
        (fun w : Fin (m.succ) → Fin (2 * m.succ) =>
          ¬ (F.filter (fun S => ∀ T ∈ F, wgt w S ≤ wgt w T)).card = 1)).card
        ≤ 2 * ((m.succ) * (2 * m.succ) ^ m) := by
      have hmem := Nat.add_le_add_left hBle ((m.succ) * (2 * m.succ) ^ m)
      rwa [show (m.succ) * (2 * m.succ) ^ m + (m.succ) * (2 * m.succ) ^ m
        = 2 * ((m.succ) * (2 * m.succ) ^ m) from by ring] at hmem
    rw [hJK]
    exact h2
  have hG : (m.succ) * (2 * m.succ) ^ m ≤ (Finset.univ.filter
      (fun w : Fin (m.succ) → Fin (2 * m.succ) =>
        (F.filter (fun S => ∀ T ∈ F, wgt w S ≤ wgt w T)).card = 1)).card := by
    have h3 : (m.succ) * (2 * m.succ) ^ m + (Finset.univ.filter
        (fun w : Fin (m.succ) → Fin (2 * m.succ) =>
          ¬ (F.filter (fun S => ∀ T ∈ F, wgt w S ≤ wgt w T)).card = 1)).card
        ≤ (Finset.univ.filter (fun w : Fin (m.succ) → Fin (2 * m.succ) =>
          (F.filter (fun S => ∀ T ∈ F, wgt w S ≤ wgt w T)).card = 1)).card +
          (Finset.univ.filter (fun w : Fin (m.succ) → Fin (2 * m.succ) =>
            ¬ (F.filter (fun S => ∀ T ∈ F, wgt w S ≤ wgt w T)).card = 1)).card := by
      rw [hpart]
      exact hM
    exact Nat.le_of_add_le_add_right h3
  have hKpos : (0:ℚ) < ((((m.succ) * (2 * m.succ) ^ m : ℕ)) : ℚ) := by
    have hposN : 0 < (m.succ) * (2 * m.succ) ^ m :=
      Nat.mul_pos (Nat.succ_pos m) (pow_pos (show 0 < 2 * m.succ by omega) m)
    exact Nat.cast_pos.mpr hposN
  have hGK : ((((m.succ) * (2 * m.succ) ^ m : ℕ)) : ℚ)
      ≤ ((Finset.univ.filter (fun w : Fin (m.succ) → Fin (2 * m.succ) =>
        (F.filter (fun S => ∀ T ∈ F, wgt w S ≤ wgt w T)).card = 1)).card : ℚ) :=
    Nat.cast_le.mpr hG
  have h2M : (0:ℚ) < 2 * ((((m.succ) * (2 * m.succ) ^ m : ℕ)) : ℚ) := by linarith
  have hhalf : ((((m.succ) * (2 * m.succ) ^ m : ℕ)) : ℚ)
      / (2 * ((((m.succ) * (2 * m.succ) ^ m : ℕ)) : ℚ)) = 1 / 2 := by
    have hne : (2:ℚ) * ((((m.succ) * (2 * m.succ) ^ m : ℕ)) : ℚ) ≠ 0 := ne_of_gt h2M
    field_simp
  have hCARD : ((Fintype.card (Fin (m.succ) → Fin (2 * m.succ))) : ℚ)
      = 2 * ((((m.succ) * (2 * m.succ) ^ m : ℕ)) : ℚ) := by
    rw [hJK]
    push_cast
    ring
  rw [hCARD, ← hhalf]
  exact div_le_div_of_nonneg_right hGK (by positivity)

/-- **Isolation lemma.** Let $n \ge 1$ and let $\mathcal{F}$ be a nonempty family of subsets of
$\{0, 1, \dots, n - 1\}$. Assign each element $i$ a weight $w(i) \in \{1, 2, \dots, 2n\}$ and give
a set $S$ the weight $w(S) = \sum_{i \in S} w(i)$. Then, among all $(2n)^n$ weight functions $w$,
the fraction for which exactly one member of $\mathcal{F}$ has minimum weight is at least $1/2$.

Equivalently, if the weights are chosen independently and uniformly at random, the
minimum-weight member of $\mathcal{F}$ is unique with probability at least $1/2$.

Proves `Wanted` entry `isolation_lemma`.

Source: https://en.wikipedia.org/wiki/Isolation_lemma
-/
theorem isolation_lemma {n : ℕ} (hn : 0 < n)
    (F : Finset (Finset (Fin n))) (hF : F.Nonempty) :
    (((Finset.univ.filter (fun w : Fin n → Fin (2 * n) =>
      (F.filter (fun S => ∀ T ∈ F,
        ∑ i ∈ S, ((w i).val + 1) ≤ ∑ i ∈ T, ((w i).val + 1))).card = 1)).card : ℚ)
      / (Fintype.card (Fin n → Fin (2 * n)) : ℚ)) ≥ 1 / 2 := by
  exact isolation_core hn F hF

end MetaMathlibExt
