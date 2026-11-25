/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.Order
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
import Mathlib.Tactic.LinearCombination

/-! # Restricted-growth word multivariate generating function

This file proves the product formula for the multivariate generating function of
restricted-growth words with prescribed letter multiplicities.
-/

@[expose] public section

namespace MetaMathlibExt

private def rgwFrom (m : ℕ) {n k : ℕ} (u : Fin n → Fin k) : Prop :=
  ∀ i : Fin n, (u i : ℕ) ≤ m ∨ ∃ j : Fin n, j < i ∧ (u i : ℕ) ≤ (u j : ℕ) + 1

private noncomputable def rgwCount (k n m : ℕ) (e : Fin k → ℕ) : ℕ :=
  Nat.card {u : Fin n → Fin k //
    rgwFrom m u ∧ ∀ a : Fin k, Nat.card {i : Fin n // u i = a} = e a}

private theorem rgw_from_cons_iff (k n m : ℕ) (a : Fin k) (w : Fin n → Fin k) :
    rgwFrom m (Fin.cons (α := fun _ => Fin k) a w) ↔
      (a : ℕ) ≤ m ∧ rgwFrom (max m ((a : ℕ) + 1)) w := by
  unfold rgwFrom
  rw [Fin.forall_fin_succ]
  constructor
  · intro h
    obtain ⟨h0, hs⟩ := h
    rw [Fin.cons_zero] at h0
    have ha : (a : ℕ) ≤ m := by
      rcases h0 with hle | ⟨j, hjlt, _⟩
      · exact hle
      · exact absurd hjlt (Fin.not_lt_zero j)
    refine ⟨ha, fun i => ?_⟩
    have hi := hs i
    rw [Fin.cons_succ] at hi
    rcases hi with hle | hex
    · exact Or.inl (hle.trans (le_max_left m _))
    · rw [Fin.exists_fin_succ] at hex
      rcases hex with ⟨hlt0, hle0⟩ | ⟨j', hjlt, hle⟩
      · rw [Fin.cons_zero] at hle0
        exact Or.inl ((le_max_iff).mpr (Or.inr hle0))
      · rw [Fin.succ_lt_succ_iff] at hjlt
        rw [Fin.cons_succ] at hle
        exact Or.inr ⟨j', hjlt, hle⟩
  · intro h
    obtain ⟨ha, hw⟩ := h
    refine ⟨?_, fun i => ?_⟩
    · rw [Fin.cons_zero]
      exact Or.inl ha
    · rw [Fin.cons_succ]
      have hi := hw i
      rcases hi with hle | ⟨j', hjlt, hle⟩
      · rcases (le_max_iff.mp hle) with h1 | h2
        · exact Or.inl h1
        · exact Or.inr ⟨0, Fin.succ_pos i, by rwa [Fin.cons_zero]⟩
      · exact Or.inr ⟨j'.succ, by rwa [Fin.succ_lt_succ_iff], by rwa [Fin.cons_succ]⟩

private theorem rgw_card_cons_fiber (k n : ℕ) (a b : Fin k) (w : Fin n → Fin k) :
    Nat.card {i : Fin (n+1) // Fin.cons (α := fun _ => Fin k) a w i = b} =
      (if a = b then 1 else 0) + Nat.card {i : Fin n // w i = b} := by
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Fintype.card_subtype, Fin.card_filter_univ_succ']
  simp only [Fin.cons_zero, Fin.cons_succ]
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]

private theorem rgw_count_zero (k m : ℕ) (e : Fin k → ℕ) :
    rgwCount k 0 m e = (if ∀ a, e a = 0 then 1 else 0) := by
  unfold rgwCount
  have hempty : ∀ u : Fin 0 → Fin k,
      (rgwFrom m u ∧ ∀ b : Fin k, Nat.card {i : Fin 0 // u i = b} = e b) ↔
        ∀ a, e a = 0 := by
    intro u
    constructor
    · rintro ⟨_, hcard⟩ a
      have h2 := hcard a
      rw [Nat.card_of_isEmpty] at h2
      omega
    · intro h
      refine ⟨fun i => i.elim0, fun b => ?_⟩
      have hz : Nat.card {i : Fin 0 // u i = b} = 0 := Nat.card_of_isEmpty
      have hb := h b
      omega
  by_cases h : ∀ a, e a = 0
  · rw [ite_eq_left h, Nat.card_eq_one_iff_unique]
    exact ⟨⟨fun ⟨u, _⟩ ⟨v, _⟩ => Subtype.ext (funext fun i => i.elim0)⟩,
      ⟨⟨fun i => i.elim0, (hempty _).mpr h⟩⟩⟩
  · rw [ite_eq_right h, Nat.card_eq_zero]
    exact Or.inl ⟨fun ⟨u, hu⟩ => h ((hempty u).mp hu)⟩

private theorem rgw_fiber_pred_pos (k n m : ℕ) (e : Fin k → ℕ) (a : Fin k)
    (ha : (a : ℕ) ≤ m) (he : 1 ≤ e a) (w : Fin n → Fin k) :
    (rgwFrom m (Fin.cons (α := fun _ => Fin k) a w) ∧
      ∀ b, Nat.card {i : Fin (n+1) // Fin.cons (α := fun _ => Fin k) a w i = b} = e b) ↔
    (rgwFrom (max m ((a : ℕ) + 1)) w ∧
      ∀ b, Nat.card {i : Fin n // w i = b} = Function.update e a (e a - 1) b) := by
  have hmul : ∀ b : Fin k,
      ((if a = b then 1 else 0) + Nat.card {i : Fin n // w i = b} = e b) ↔
      (Nat.card {i : Fin n // w i = b} = Function.update e a (e a - 1) b) := by
    intro b
    by_cases hab : a = b
    · subst hab
      simp only [Function.update_self, ↓reduceIte]
      omega
    · have hne : b ≠ a := fun h => hab h.symm
      simp only [Function.update_of_ne hne, hab, ↓reduceIte, zero_add]
  rw [rgw_from_cons_iff]
  constructor
  · rintro ⟨⟨-, hgr⟩, hcard⟩
    refine ⟨hgr, fun b => ?_⟩
    have hb := hcard b
    rw [rgw_card_cons_fiber] at hb
    exact (hmul b).mp hb
  · rintro ⟨hgr, hcard⟩
    refine ⟨⟨ha, hgr⟩, fun b => ?_⟩
    rw [rgw_card_cons_fiber]
    exact (hmul b).mpr (hcard b)

private def rgwSplitEquiv (k n : ℕ) :
    (Fin (n+1) → Fin k) ≃ Fin k × (Fin n → Fin k) where
  toFun u := (u 0, fun i => u i.succ)
  invFun := fun p => Fin.cons (α := fun _ => Fin k) p.1 p.2
  left_inv u := Fin.cons_self_tail u
  right_inv := by
    rintro ⟨a, w⟩
    refine Prod.ext ?_ ?_
    · change Fin.cons (α := fun _ => Fin k) a w 0 = a
      exact Fin.cons_zero _ _
    · change (fun i => Fin.cons (α := fun _ => Fin k) a w i.succ) = w
      funext i
      exact Fin.cons_succ _ _ i

private theorem rgw_split_pred (k n m : ℕ) (e : Fin k → ℕ) (u : Fin (n + 1) → Fin k) :
    (rgwFrom m u ∧ ∀ b, Nat.card {i : Fin (n+1) // u i = b} = e b) ↔
    (rgwFrom m (Fin.cons (α := fun _ => Fin k) (rgwSplitEquiv k n u).1
        (rgwSplitEquiv k n u).2) ∧
      ∀ b, Nat.card {i : Fin (n+1) //
        Fin.cons (α := fun _ => Fin k) (rgwSplitEquiv k n u).1
          (rgwSplitEquiv k n u).2 i = b} = e b) := by
  have h : Fin.cons (α := fun _ => Fin k) (rgwSplitEquiv k n u).1
      (rgwSplitEquiv k n u).2 = u :=
    (rgwSplitEquiv k n).symm_apply_apply u
  rw [h]

private theorem rgw_count_succ (k n m : ℕ) (e : Fin k → ℕ) :
    rgwCount k (n+1) m e = ∑ a : Fin k,
      (if (a : ℕ) ≤ m ∧ 1 ≤ e a then
        rgwCount k n (max m ((a : ℕ)+1)) (Function.update e a (e a - 1)) else 0) := by
  have hpair : {u : Fin (n+1) → Fin k //
        rgwFrom m u ∧ ∀ b, Nat.card {i : Fin (n+1) // u i = b} = e b} ≃
      (a : Fin k) × {w : Fin n → Fin k //
        rgwFrom m (Fin.cons (α := fun _ => Fin k) a w) ∧
        ∀ b, Nat.card {i : Fin (n+1) // Fin.cons (α := fun _ => Fin k) a w i = b} = e b} :=
    (Equiv.subtypeEquiv (rgwSplitEquiv k n) (fun u => rgw_split_pred k n m e u)).trans
      (Equiv.subtypeProdEquivSigmaSubtype _)
  unfold rgwCount
  rw [Nat.card_congr hpair, Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hcon : (a : ℕ) ≤ m ∧ 1 ≤ e a
  · obtain ⟨ha, he⟩ := hcon
    rw [ite_eq_left ⟨ha, he⟩]
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro w
    exact rgw_fiber_pred_pos k n m e a ha he w
  · rw [ite_eq_right hcon]
    rw [Nat.card_eq_zero]
    refine Or.inl ⟨?_⟩
    rintro ⟨w, hgr, hmul⟩
    by_cases ham : (a : ℕ) ≤ m
    · have he : e a = 0 := by omega
      have haa := hmul a
      rw [rgw_card_cons_fiber] at haa
      have h1 : (if a = a then (1 : ℕ) else 0) = 1 := ite_eq_left rfl
      rw [h1] at haa
      omega
    · rw [rgw_from_cons_iff] at hgr
      exact ham hgr.1

private def rgwShift (k m : ℕ) (c : Fin k →₀ ℕ) : Fin k → ℕ :=
  fun a => c a + (if m ≤ (a : ℕ) then 1 else 0)

private theorem rgw_finsupp_sum_tsub_single_a (k : ℕ) (c : Fin k →₀ ℕ) (a : Fin k)
    (h : 1 ≤ c a) :
    (c - Finsupp.single a (1 : ℕ)).sum (fun _ x => x) + 1 = c.sum (fun _ x => x) := by
  have hle : Finsupp.single a (1 : ℕ) ≤ c := Finsupp.single_le_iff.mpr h
  have hcs : c - Finsupp.single a (1 : ℕ) + Finsupp.single a (1 : ℕ) = c :=
    tsub_add_cancel_of_le hle
  have hsum : (c - Finsupp.single a (1 : ℕ) + Finsupp.single a (1 : ℕ)).sum
      (fun _ x => x) = c.sum (fun _ x => x) :=
    congrArg (fun f : Fin k →₀ ℕ => f.sum (fun _ x => x)) hcs
  have hadd : ((c - Finsupp.single a (1 : ℕ) + Finsupp.single a (1 : ℕ)).sum
      (fun _ x => x)) = ((c - Finsupp.single a (1 : ℕ)).sum (fun _ x => x) +
      (Finsupp.single a (1 : ℕ)).sum (fun _ x => x)) :=
    Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)
  rw [hadd] at hsum
  have h2 : (Finsupp.single a (1 : ℕ)).sum (fun _ x => x) = 1 :=
    Finsupp.sum_single_index rfl
  rw [h2] at hsum
  exact hsum

private theorem rgw_finsupp_sum_tsub_single_b (k : ℕ) (c : Fin k →₀ ℕ)
    (h : c.sum (fun _ x => x) = 0) : c = 0 := by
  have hfin : ∑ i : Fin k, c i = 0 := by
    have hft := Finsupp.sum_fintype c (fun _ x => x) (fun _ => rfl)
    rw [h] at hft
    simpa using hft.symm
  have hall : ∀ i ∈ (Finset.univ : Finset (Fin k)), c i = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Nat.zero_le _)).mp hfin
  apply Finsupp.ext
  intro a
  simpa using hall a (Finset.mem_univ a)

private theorem rgw_shift_lt (k m : ℕ) (c : Fin k →₀ ℕ) (a : Fin k) (h : (a : ℕ) < m) :
    rgwShift k m c a = c a := by
  unfold rgwShift
  rw [ite_eq_right (Nat.not_le.mpr h), add_zero]

private theorem rgw_shift_ge (k m : ℕ) (c : Fin k →₀ ℕ) (a : Fin k) (h : m ≤ (a : ℕ)) :
    rgwShift k m c a = c a + 1 := by
  unfold rgwShift
  rw [ite_eq_left h]

private theorem rgw_shift_update_lt (k m : ℕ) (c : Fin k →₀ ℕ) (a : Fin k)
    (h : (a : ℕ) < m) :
    Function.update (rgwShift k m c) a (rgwShift k m c a - 1) =
      rgwShift k m (c - Finsupp.single a (1 : ℕ)) := by
  funext b
  by_cases hab : b = a
  · rw [hab]
    rw [Function.update_self, rgw_shift_lt k m c a h,
      rgw_shift_lt k m (c - Finsupp.single a (1 : ℕ)) a h,
      Finsupp.tsub_apply, Finsupp.single_eq_same]
  · rw [Function.update_of_ne hab]
    have hts : ((c - Finsupp.single a (1 : ℕ)) : Fin k →₀ ℕ) b = c b := by
      rw [Finsupp.tsub_apply, Finsupp.single_eq_of_ne hab, Nat.sub_zero]
    unfold rgwShift
    rw [hts]

private theorem rgw_shift_update_eq (k m : ℕ) (c : Fin k →₀ ℕ) (a : Fin k)
    (hm : (a : ℕ) = m) :
    Function.update (rgwShift k m c) a (rgwShift k m c a - 1) =
      rgwShift k (m + 1) c := by
  funext b
  by_cases hab : b = a
  · rw [hab]
    rw [Function.update_self, rgw_shift_ge k m c a hm.symm.le]
    have h1 : ¬ (m + 1 ≤ (a : ℕ)) := by omega
    unfold rgwShift
    rw [ite_eq_right h1, add_zero]
    exact Nat.add_sub_cancel _ _
  · rw [Function.update_of_ne hab]
    have hne : (b : ℕ) ≠ (a : ℕ) := fun h => hab (Fin.ext_iff.mpr h)
    unfold rgwShift
    by_cases hmb : m ≤ (b : ℕ)
    · have hmb2 : m + 1 ≤ (b : ℕ) := by omega
      rw [ite_eq_left hmb, ite_eq_left hmb2]
    · have hmb2 : ¬ (m + 1 ≤ (b : ℕ)) := by omega
      rw [ite_eq_right hmb, ite_eq_right hmb2]

private theorem rgw_shift_top_zero (k : ℕ) (a : Fin k) :
    rgwShift k k 0 a = 0 := by
  unfold rgwShift
  have h : ¬ (k ≤ (a : ℕ)) := Nat.not_le.mpr (Fin.is_lt a)
  rw [ite_eq_right h, add_zero]
  rfl

private theorem rgw_coeff_X_mul {σ : Type*} {R : Type*} [Semiring R] (s : σ)
    (φ : MvPowerSeries σ R) (c : σ →₀ ℕ) :
    MvPowerSeries.coeff c (MvPowerSeries.X s * φ) =
      (if 1 ≤ c s then MvPowerSeries.coeff (c - Finsupp.single s 1) φ else 0) := by
  rw [MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul]
  by_cases h : Finsupp.single s (1 : ℕ) ≤ c
  · rw [ite_eq_left h]
    have h2 : 1 ≤ c s := Finsupp.single_le_iff.mp h
    rw [ite_eq_left h2, one_mul]
  · rw [ite_eq_right h]
    have h2 : ¬ (1 ≤ c s) := fun hh => h (Finsupp.single_le_iff.mpr hh)
    rw [ite_eq_right h2]

private noncomputable def rgwCoeff (k m : ℕ) (c : Fin k →₀ ℕ) : ℕ :=
  rgwCount k ((k - m) + c.sum (fun _ x => x)) m (rgwShift k m c)

private theorem rgw_count_succ_term (k m : ℕ) (_hm : m ≤ k) (c : Fin k →₀ ℕ) (n' : ℕ)
    (hlen : n' + 1 = (k - m) + c.sum (fun _ x => x)) (a : Fin k) :
    (if (a : ℕ) ≤ m ∧ 1 ≤ rgwShift k m c a then
      rgwCount k n' (max m ((a : ℕ) + 1))
        (Function.update (rgwShift k m c) a (rgwShift k m c a - 1)) else 0) =
    (if (a : ℕ) < m ∧ 1 ≤ c a then rgwCoeff k m (c - Finsupp.single a (1 : ℕ))
      else 0) +
    (if (a : ℕ) = m then rgwCoeff k (m + 1) c else 0) := by
  by_cases halt : (a : ℕ) < m
  · have ham : (a : ℕ) ≤ m := halt.le
    have hshift : rgwShift k m c a = c a := rgw_shift_lt k m c a halt
    have hne : ¬ ((a : ℕ) = m) := by omega
    have hmax : max m ((a : ℕ) + 1) = m := max_eq_left (by omega)
    have hupd : Function.update (rgwShift k m c) a (rgwShift k m c a - 1) =
        rgwShift k m (c - Finsupp.single a (1 : ℕ)) :=
      rgw_shift_update_lt k m c a halt
    by_cases hc : 1 ≤ c a
    · have hLHS : (a : ℕ) ≤ m ∧ 1 ≤ rgwShift k m c a :=
        ⟨ham, by rw [hshift]; exact hc⟩
      rw [ite_eq_left hLHS, ite_eq_left ⟨halt, hc⟩, ite_eq_right hne, hmax, hupd]
      have h5 : (c - Finsupp.single a (1 : ℕ)).sum (fun _ x => x) + 1 =
          c.sum (fun _ x => x) := rgw_finsupp_sum_tsub_single_a k c a hc
      have hlen2 : n' = (k - m) + (c - Finsupp.single a (1 : ℕ)).sum (fun _ x => x) := by
        omega
      have hcoeff : rgwCount k n' m (rgwShift k m (c - Finsupp.single a (1 : ℕ))) =
          rgwCoeff k m (c - Finsupp.single a (1 : ℕ)) := by
        unfold rgwCoeff
        rw [hlen2]
      rw [hcoeff, add_zero]
    · have hLHSneg : ¬ ((a : ℕ) ≤ m ∧ 1 ≤ rgwShift k m c a) :=
        fun hcon => hc (by rw [← hshift]; exact hcon.2)
      rw [ite_eq_right hLHSneg, ite_eq_right (fun hcon => hc hcon.2), ite_eq_right hne]
  · by_cases heq : (a : ℕ) = m
    · have hmk : m < k := by
        have hlt := Fin.is_lt a
        omega
      have hLHS : (a : ℕ) ≤ m ∧ 1 ≤ rgwShift k m c a :=
        ⟨heq.le, by rw [rgw_shift_ge k m c a heq.ge]; omega⟩
      have hRHS1 : ¬ ((a : ℕ) < m) := by omega
      have hRHS1neg : ¬ ((a : ℕ) < m ∧ 1 ≤ c a) := fun hcon => hRHS1 hcon.1
      have hmax : max m ((a : ℕ) + 1) = m + 1 := by
        rw [heq]
        exact max_eq_right (Nat.le_succ m)
      have hupd : Function.update (rgwShift k m c) a (rgwShift k m c a - 1) =
          rgwShift k (m + 1) c := rgw_shift_update_eq k m c a heq
      rw [ite_eq_left hLHS, ite_eq_right hRHS1neg, ite_eq_left heq, hmax, hupd]
      have hlen2 : n' = (k - (m + 1)) + c.sum (fun _ x => x) := by omega
      have hcoeff : rgwCount k n' (m + 1) (rgwShift k (m + 1) c) =
          rgwCoeff k (m + 1) c := by
        unfold rgwCoeff
        rw [hlen2]
      rw [hcoeff, zero_add]
    · have hnm : ¬ ((a : ℕ) ≤ m) := by omega
      rw [ite_eq_right (fun hcon => hnm hcon.1), ite_eq_right (fun hcon => halt hcon.1),
        ite_eq_right heq]

private theorem rgw_sum_ite_eq (k m : ℕ) (F : ℕ) :
    (∑ a : Fin k, (if (a : ℕ) = m then F else 0)) = (if m < k then F else 0) := by
  by_cases hmk : m < k
  · rw [ite_eq_left hmk]
    have h0 : ∀ x : Fin k, x ≠ (⟨m, hmk⟩ : Fin k) →
        (if (x : ℕ) = m then F else 0) = 0 := by
      intro x hx
      exact ite_eq_right (fun hcon => hx (Fin.ext hcon))
    have h1 : (if ((⟨m, hmk⟩ : Fin k) : ℕ) = m then F else 0) = F :=
      ite_eq_left rfl
    rw [Fintype.sum_eq_single (⟨m, hmk⟩ : Fin k) h0]
    exact h1
  · rw [ite_eq_right hmk]
    apply Finset.sum_eq_zero
    intro a _
    exact ite_eq_right (fun hcon : (a : ℕ) = m => hmk (hcon ▸ Fin.is_lt a))

private theorem rgw_coeff_rec (k m : ℕ) (hm : m ≤ k) (c : Fin k →₀ ℕ) :
    rgwCoeff k m c =
      (∑ a : Fin k, (if (a : ℕ) < m ∧ 1 ≤ c a then
        rgwCoeff k m (c - Finsupp.single a (1 : ℕ)) else 0))
      + (if m < k then rgwCoeff k (m + 1) c else (if c = 0 then 1 else 0)) := by
  by_cases hL : (k - m) + c.sum (fun _ x => x) = 0
  · have hkm : k - m = 0 := by omega
    have hsum : c.sum (fun _ x => x) = 0 := by omega
    have hc : c = 0 := rgw_finsupp_sum_tsub_single_b k c hsum
    have hmk : m = k := by omega
    rw [hmk, hc]
    have hs0 : (∑ a : Fin k, (if (a : ℕ) < k ∧ 1 ≤ (0 : Fin k →₀ ℕ) a then
        rgwCoeff k k (0 - Finsupp.single a (1 : ℕ)) else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro a _
      have hz : (0 : Fin k →₀ ℕ) a = 0 := by simp
      exact ite_eq_right (fun hcon => by rw [hz] at hcon; omega)
    rw [hs0]
    have hlen : (k - k) + (0 : Fin k →₀ ℕ).sum (fun _ x => x) = 0 := by simp
    have e1 : rgwCoeff k k (0 : Fin k →₀ ℕ) =
        rgwCount k ((k - k) + (0 : Fin k →₀ ℕ).sum (fun _ x => x)) k
          (rgwShift k k 0) := rfl
    rw [e1, hlen, rgw_count_zero]
    have hshift : (∀ a : Fin k, rgwShift k k (0 : Fin k →₀ ℕ) a = 0) :=
      fun a => rgw_shift_top_zero k a
    rw [ite_eq_left hshift]
    have hkk : ¬ (k < k) := by omega
    rw [ite_eq_right hkk]
    have hc0 : ((0 : Fin k →₀ ℕ) = 0) := rfl
    rw [ite_eq_left hc0]
  · obtain ⟨n', hn'⟩ := Nat.exists_eq_succ_of_ne_zero hL
    have e1 : rgwCoeff k m c =
        rgwCount k ((k - m) + c.sum (fun _ x => x)) m (rgwShift k m c) := rfl
    rw [e1, hn', rgw_count_succ k n' m (rgwShift k m c),
      Finset.sum_congr rfl (fun a _ => rgw_count_succ_term k m hm c n' hn'.symm a),
      Finset.sum_add_distrib, rgw_sum_ite_eq k m (rgwCoeff k (m + 1) c)]
    by_cases hmk : m < k
    · rw [ite_eq_left hmk, ite_eq_left hmk]
    · have hc0 : c ≠ 0 := by
        rintro rfl
        simp at hn'
        omega
      rw [ite_eq_right hmk, ite_eq_right hmk, ite_eq_right hc0]

private noncomputable def rgwSeries (k m : ℕ) : MvPowerSeries (Fin k) ℚ :=
  fun c => ((rgwCoeff k m c : ℕ) : ℚ)

private noncomputable def rgwPartialSum (k m : ℕ) : MvPowerSeries (Fin k) ℚ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin k => (i : ℕ) < m), MvPowerSeries.X i

private theorem rgw_coeff_rec_cast (k m : ℕ) (hm : m ≤ k) (c : Fin k →₀ ℕ) :
    ((rgwCoeff k m c : ℕ) : ℚ) =
      (∑ a : Fin k, (if (a : ℕ) < m ∧ 1 ≤ c a then
        ((rgwCoeff k m (c - Finsupp.single a (1 : ℕ)) : ℕ) : ℚ) else 0))
      + (if m < k then ((rgwCoeff k (m + 1) c : ℕ) : ℚ)
        else (if c = 0 then 1 else 0)) := by
  have h := congrArg (fun n : ℕ => ((n : ℕ) : ℚ)) (rgw_coeff_rec k m hm c)
  push_cast at h
  exact h

private theorem rgw_ite_and (k m : ℕ) (c : Fin k →₀ ℕ) (i : Fin k) :
    (if (i : ℕ) < m then
      (if 1 ≤ c i then ((rgwCoeff k m (c - Finsupp.single i 1) : ℕ) : ℚ) else 0)
      else 0) =
    (if (i : ℕ) < m ∧ 1 ≤ c i then
      ((rgwCoeff k m (c - Finsupp.single i 1) : ℕ) : ℚ) else 0) := by
  by_cases h1 : (i : ℕ) < m <;> by_cases h2 : 1 ≤ c i
  · rw [ite_eq_left h1, ite_eq_left h2, ite_eq_left ⟨h1, h2⟩]
  · rw [ite_eq_left h1, ite_eq_right h2, ite_eq_right (fun h => h2 h.2)]
  · rw [ite_eq_right h1, ite_eq_right (fun h => h1 h.1)]
  · rw [ite_eq_right h1, ite_eq_right (fun h => h1 h.1)]

private theorem rgw_series_eq (k m : ℕ) (hm : m ≤ k) :
    rgwSeries k m = rgwPartialSum k m * rgwSeries k m +
      (if m < k then rgwSeries k (m + 1) else 1) := by
  have h1sum : ∀ c : Fin k →₀ ℕ,
      MvPowerSeries.coeff c (rgwPartialSum k m * rgwSeries k m) =
        (∑ i ∈ Finset.univ.filter (fun i : Fin k => (i : ℕ) < m),
          (if 1 ≤ c i then ((rgwCoeff k m (c - Finsupp.single i 1) : ℕ) : ℚ)
            else 0)) := by
    intro c
    unfold rgwPartialSum
    rw [Finset.sum_mul, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [rgw_coeff_X_mul]
    rfl
  have htail : ∀ c : Fin k →₀ ℕ,
      MvPowerSeries.coeff c (if m < k then rgwSeries k (m + 1) else 1) =
        (if m < k then ((rgwCoeff k (m + 1) c : ℕ) : ℚ)
          else (if c = 0 then 1 else 0)) := by
    intro c
    by_cases hmk : m < k
    · rw [ite_eq_left hmk, ite_eq_left hmk]
      rfl
    · rw [ite_eq_right hmk, ite_eq_right hmk]
      exact MvPowerSeries.coeff_one c
  apply MvPowerSeries.ext
  intro c
  change ((rgwCoeff k m c : ℕ) : ℚ) = _
  have hsum_eq : (∑ i : Fin k,
        (if (i : ℕ) < m then
          (if 1 ≤ c i then ((rgwCoeff k m (c - Finsupp.single i 1) : ℕ) : ℚ) else 0)
          else 0)) =
      (∑ a : Fin k, (if (a : ℕ) < m ∧ 1 ≤ c a then
        ((rgwCoeff k m (c - Finsupp.single a (1 : ℕ)) : ℕ) : ℚ) else 0)) :=
    Finset.sum_congr rfl (fun i _ => rgw_ite_and k m c i)
  rw [map_add, h1sum c, Finset.sum_filter, hsum_eq, htail c,
    rgw_coeff_rec_cast k m hm c]

private theorem rgw_constCoeff_ne (k m : ℕ) :
    MvPowerSeries.constantCoeff (1 - rgwPartialSum k m) ≠ 0 := by
  have hP : MvPowerSeries.constantCoeff (rgwPartialSum k m) = 0 := by
    unfold rgwPartialSum
    simp [map_sum, MvPowerSeries.constantCoeff_X]
  simp [map_sub, hP]

private theorem rgw_series_eq_mul_inv (k m : ℕ) (hm : m ≤ k) :
    rgwSeries k m = (if m < k then rgwSeries k (m + 1) else 1) *
      (1 - rgwPartialSum k m)⁻¹ := by
  rw [MvPowerSeries.eq_mul_inv_iff_mul_eq (rgw_constCoeff_ne k m)]
  have h := rgw_series_eq k m hm
  linear_combination h

private theorem rgw_series_eq_prod_aux (k : ℕ) (d : ℕ) :
    ∀ m : ℕ, m ≤ k → k - m = d →
      rgwSeries k m = ∏ j ∈ Finset.Ico m (k + 1), (1 - rgwPartialSum k j)⁻¹ := by
  induction d with
  | zero =>
      intro m hm hkm
      have hmk : m = k := by omega
      have h11 := rgw_series_eq_mul_inv k m hm
      rw [hmk] at h11 ⊢
      rw [ite_eq_right (by omega : ¬ k < k)] at h11
      rw [h11, one_mul, Finset.prod_eq_prod_Ico_succ_bot (Nat.lt_succ_self k) _,
        Finset.Ico_self, Finset.prod_empty, mul_one]
  | succ n ih =>
      intro m hm hkm
      have hmk : m < k := by omega
      have hm1 : m + 1 ≤ k := by omega
      have hkd : k - (m + 1) = n := by omega
      have ih' := ih (m + 1) hm1 hkd
      have h11 := rgw_series_eq_mul_inv k m hm
      rw [ite_eq_left hmk] at h11
      rw [h11, ih',
        Finset.prod_eq_prod_Ico_succ_bot (by omega : m < k + 1) _]
      exact mul_comm _ _

private theorem rgw_series_eq_prod (k m : ℕ) (hm : m ≤ k) :
    rgwSeries k m = ∏ j ∈ Finset.Ico m (k + 1), (1 - rgwPartialSum k j)⁻¹ :=
  rgw_series_eq_prod_aux k (k - m) m hm rfl

private theorem rgw_prod_reindex (k : ℕ) :
    (∏ j ∈ Finset.Ico 0 (k + 1), (1 - rgwPartialSum k j)⁻¹) =
    ∏ j : Fin k, (1 - ∑ i ∈ Finset.Iic j, MvPowerSeries.X i)⁻¹ := by
  have hP0 : rgwPartialSum k 0 = 0 := by
    unfold rgwPartialSum
    rw [Finset.filter_false_of_mem (fun i _ => Nat.not_lt_zero _)]
    exact Finset.sum_empty
  have h1 : ((1 : MvPowerSeries (Fin k) ℚ)⁻¹) = 1 := by
    have hc : MvPowerSeries.constantCoeff (1 : MvPowerSeries (Fin k) ℚ) ≠ 0 := by
      rw [MvPowerSeries.constantCoeff_one]
      exact one_ne_zero
    rw [MvPowerSeries.inv_eq_iff_mul_eq_one hc]
    exact one_mul 1
  have hf0 : (1 - rgwPartialSum k 0)⁻¹ = 1 := by
    rw [hP0, sub_zero]
    exact h1
  have hfilter : ∀ j : Fin k,
      Finset.univ.filter (fun i : Fin k => (i : ℕ) < (j : ℕ) + 1) = Finset.Iic j := by
    intro j
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iic,
      Fin.le_iff_val_le_val]
    omega
  rw [← Finset.range_eq_Ico, Finset.prod_range_succ' _ k, hf0, mul_one,
    ← Fin.prod_univ_eq_prod_range]
  apply Finset.prod_congr rfl
  intro j _
  unfold rgwPartialSum
  rw [hfilter j]

private theorem rgw_wanted_lhs_eq (k : ℕ) :
    ((fun d : Fin k →₀ ℕ =>
      (Nat.card {
        u : Fin (k + d.sum fun _ m => m) → Fin k //
          (∀ i, (u i : ℕ) = 0 ∨
            ∃ j, j < i ∧ (u i : ℕ) ≤ (u j : ℕ) + 1) ∧
          ∀ a, Nat.card {i : Fin (k + d.sum fun _ m => m) // u i = a} = d a + 1
      } : ℚ)) : MvPowerSeries (Fin k) ℚ) = rgwSeries k 0 := by
  apply MvPowerSeries.ext
  intro d
  change ((Nat.card {
        u : Fin (k + d.sum fun _ m => m) → Fin k //
          (∀ i, (u i : ℕ) = 0 ∨
            ∃ j, j < i ∧ (u i : ℕ) ≤ (u j : ℕ) + 1) ∧
          ∀ a, Nat.card {i : Fin (k + d.sum fun _ m => m) // u i = a} = d a + 1
      } : ℕ) : ℚ) = _
  change ((Nat.card {
        u : Fin (k + d.sum fun _ m => m) → Fin k //
          (∀ i, (u i : ℕ) = 0 ∨
            ∃ j, j < i ∧ (u i : ℕ) ≤ (u j : ℕ) + 1) ∧
          ∀ a, Nat.card {i : Fin (k + d.sum fun _ m => m) // u i = a} = d a + 1
      } : ℕ) : ℚ) = ((rgwCoeff k 0 d : ℕ) : ℚ)
  rw [Nat.cast_inj]
  have hgrowth : ∀ u : Fin (k + d.sum fun _ m => m) → Fin k,
      rgwFrom 0 u ↔ (∀ i, (u i : ℕ) = 0 ∨
        ∃ j, j < i ∧ (u i : ℕ) ≤ (u j : ℕ) + 1) := by
    intro u
    unfold rgwFrom
    constructor
    · intro h i
      rcases h i with hle | hex
      · exact Or.inl (Nat.le_zero.mp hle)
      · exact Or.inr hex
    · intro h i
      rcases h i with hle | hex
      · exact Or.inl (Nat.le_zero.mpr hle)
      · exact Or.inr hex
  have hshift : ∀ a : Fin k, rgwShift k 0 d a = d a + 1 :=
    fun a => rgw_shift_ge k 0 d a (Nat.zero_le _)
  have e1 : rgwCoeff k 0 d =
      rgwCount k (k + d.sum (fun _ x => x)) 0 (rgwShift k 0 d) := by
    unfold rgwCoeff
    rw [Nat.sub_zero]
  rw [e1]
  unfold rgwCount
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro u
  constructor
  · rintro ⟨hgr, hmul⟩
    refine ⟨(hgrowth u).mpr hgr, fun a => ?_⟩
    rw [hshift a]
    exact hmul a
  · rintro ⟨hgr, hmul⟩
    refine ⟨(hgrowth u).mp hgr, fun a => ?_⟩
    have hmul_a := hmul a
    rw [hshift a] at hmul_a
    exact hmul_a

/-- **Restricted-growth word generating function.** Fix $k \ge 0$. A word $u_1 u_2 \cdots u_n$
in the letters $1, \dots, k$ is a restricted-growth word if for every $i$, either $u_i = 1$ or
$u_i \le u_j + 1$ for some $j < i$ (so a nonempty such word begins with $1$). For
$d = (d_1, \dots, d_k) \in \mathbb{N}^k$, let $r(d)$ be the number of restricted-growth words in
which each letter $a$ occurs exactly $d_a + 1$ times. Then, in the ring of formal power series
in $x_1, \dots, x_k$ over $\mathbb{Q}$,

$$\sum_{d} r(d)\, x_1^{d_1} \cdots x_k^{d_k} = \prod_{j=1}^{k} (1 - x_1 - \cdots - x_j)^{-1}.$$

Proof: Decompose restricted-growth words by their first letter to obtain a coefficient
recurrence, lift it to multivariate power series, and iterate power-series inverse
cancellation. The combinatorial route follows Ehrenborg, Hedmark, and Hettle, Theorem 1.

Proves `Wanted` entry `restricted_growth_word_monomial_generating_function`.

Source: Richard Ehrenborg, Dustin Hedmark, and Cyrus Hettle, "A Restricted Growth
Word Approach to Partitions with Odd/Even Size Blocks," Journal of Integer Sequences
20 (2017), Article 17.5.5, Theorem 1 (label `theorem_one`), lines 190-200,
<https://cs.uwaterloo.ca/journals/JIS/VOL20/Ehrenborg/ehren4.tex>.
-/
public theorem restricted_growth_word_monomial_generating_function
    (k : ℕ) :
    ((fun d : Fin k →₀ ℕ =>
      (Nat.card {
        u : Fin (k + d.sum fun _ m => m) → Fin k //
          (∀ i, (u i : ℕ) = 0 ∨
            ∃ j, j < i ∧ (u i : ℕ) ≤ (u j : ℕ) + 1) ∧
          ∀ a, Nat.card {i : Fin (k + d.sum fun _ m => m) // u i = a} = d a + 1
      } : ℚ)) : MvPowerSeries (Fin k) ℚ) =
      (∏ j : Fin k,
        (1 - ∑ i ∈ Finset.Iic j, MvPowerSeries.X i)⁻¹ : MvPowerSeries (Fin k) ℚ) := by
  rw [rgw_wanted_lhs_eq k, rgw_series_eq_prod k 0 (Nat.zero_le k)]
  exact rgw_prod_reindex k

end MetaMathlibExt
