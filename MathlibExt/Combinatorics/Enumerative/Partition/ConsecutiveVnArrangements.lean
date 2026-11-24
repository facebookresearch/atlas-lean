/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.Partition.DiagonalSequences
public import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.Interval.Finset.SuccPred
import Mathlib.Data.List.Chain
import Mathlib.Order.SuccPred.Int

/-!
# Vn-arrangements of consecutive integers

The number of vn-arrangements of a nonempty interval of consecutive integers doubles
each time a new maximum is added, giving the count `2 ^ (t - 1)` for an interval of size `t`.
-/

namespace MetaMathlibExt
namespace vnArrangementCount_consecutive

private abbrev arrangements (a m : ℤ) : Set (List ℤ) :=
  {l | (l : Multiset ℤ) = (Finset.Ico a m).val ∧ l.IsChain fun x y => y - x ≤ 1}

private theorem mem_iff {a m x : ℤ} {l : List ℤ}
    (h : (l : Multiset ℤ) = (Finset.Ico a m).val) : x ∈ l ↔ a ≤ x ∧ x < m := by
  rw [← Multiset.mem_coe, h, Finset.mem_val, Finset.mem_Ico]

-- Deleting the maximum restores a smaller arrangement. If there is an entry just
-- before the maximum, the step bound forces that entry to be its predecessor.
private theorem insert_max_iff {a m : ℤ} (ham : a ≤ m) (u v : List ℤ) :
    u ++ m :: v ∈ arrangements a (m + 1) ↔
      u ++ v ∈ arrangements a m ∧ ∀ x ∈ u.getLast?, x = m - 1 := by
  have hbag : ((u ++ m :: v : List ℤ) : Multiset ℤ) = m ::ₘ ↑(u ++ v) :=
    Multiset.coe_eq_coe.mpr List.perm_middle
  change (_ = _ ∧ _) ↔ (_ = _ ∧ _) ∧ _
  rw [← Finset.insert_Ico_right_eq_Ico_add_one ham, Finset.insert_val_of_notMem (by simp),
    hbag, Multiset.cons_inj_right, and_assoc]
  refine and_congr_right fun h => ?_
  have hu (x) (hx : x ∈ u.getLast?) : x < m :=
    ((mem_iff h).mp (List.mem_append_left _ (List.mem_of_mem_getLast? hx))).2
  have hv (y) (hy : y ∈ v.head?) : y < m :=
    ((mem_iff h).mp (List.mem_append_right _ (List.mem_of_mem_head? hy))).2
  simp only [List.isChain_append, List.isChain_cons, List.head?_cons, Option.mem_some_iff,
    forall_eq']
  constructor
  · rintro ⟨huChain, ⟨_, hvChain⟩, hprev⟩
    have heq (x) (hx : x ∈ u.getLast?) : x = m - 1 := by
      have := hprev x hx
      have := hu x hx
      omega
    refine ⟨⟨huChain, hvChain, fun x hx y hy => ?_⟩, heq⟩
    have := heq x hx
    have := hv y hy
    omega
  · rintro ⟨⟨huChain, hvChain, _⟩, heq⟩
    refine ⟨huChain, ⟨fun y hy => ?_, hvChain⟩, fun x hx => ?_⟩
    · have := hv y hy
      omega
    · rw [heq x hx]
      omega

-- The Boolean records whether the new maximum starts the list.
private def extend (m : ℤ) : List ℤ × Bool → List ℤ
  | (l, true) => m :: l
  | (l, false) =>
    let i := l.idxOf (m - 1) + 1
    l.take i ++ m :: l.drop i

private theorem extend_after (m : ℤ) (u v : List ℤ) (hu : m - 1 ∉ u) :
    extend m (u ++ (m - 1) :: v, false) = (u ++ [m - 1]) ++ m :: v := by
  simp [extend, List.idxOf_append_of_notMem hu, List.take_append, List.drop_append,
    List.take_of_length_le (Nat.le_succ u.length), List.drop_of_length_le (Nat.le_succ u.length)]

private def removeMax (m : ℤ) (l : List ℤ) : List ℤ × Bool :=
  (l.erase m, l.idxOf m == 0)

private theorem extend_spec {a m : ℤ} (ham : a < m) {l : List ℤ}
    (hl : l ∈ arrangements a m) (b : Bool) :
    extend m (l, b) ∈ arrangements a (m + 1) ∧ removeMax m (extend m (l, b)) = (l, b) := by
  cases b with
  | true =>
    exact ⟨(insert_max_iff ham.le [] l).mpr ⟨hl, by simp⟩, by simp [extend, removeMax]⟩
  | false =>
    have hpred : m - 1 ∈ l := (mem_iff hl.1).mpr (by omega)
    obtain ⟨u, v, rfl, hu⟩ := List.eq_append_cons_of_mem hpred
    rw [extend_after _ _ _ hu]
    have hm : m ∉ u ++ [m - 1] := by
      intro h
      have : m ∈ u ++ (m - 1) :: v := by simpa using List.mem_append_left v h
      exact (lt_irrefl m) ((mem_iff hl.1).mp this).2
    refine ⟨(insert_max_iff ham.le _ _).mpr ⟨by simpa using hl, by simp⟩, ?_⟩
    unfold removeMax
    rw [List.erase_append_right _ hm, List.idxOf_append_of_notMem hm]
    simp

private theorem extend_bijOn {a m : ℤ} (ham : a < m) :
    Set.BijOn (extend m) (arrangements a m ×ˢ Set.univ) (arrangements a (m + 1)) := by
  refine ⟨fun ⟨l, b⟩ h => (extend_spec ham h.1 b).1,
    Set.LeftInvOn.injOn (f₁' := removeMax m) (fun ⟨l, b⟩ h => (extend_spec ham h.1 b).2), ?_⟩
  intro l hl
  have hm : m ∈ l := (mem_iff hl.1).mpr (by omega)
  obtain ⟨u, v, rfl⟩ := List.append_of_mem hm
  obtain ⟨hsmall, hprev⟩ := (insert_max_iff ham.le u v).mp hl
  rcases u.eq_nil_or_concat' with rfl | ⟨w, x, rfl⟩
  · exact ⟨(v, true), ⟨hsmall, trivial⟩, rfl⟩
  · have hx : x = m - 1 := hprev x (by simp)
    subst x
    have hnodup : (w ++ (m - 1) :: v).Nodup := by
      have := Multiset.coe_nodup.mp (hsmall.1 ▸ (Finset.Ico a m).nodup)
      simpa using this
    have hw : m - 1 ∉ w := fun h => (List.nodup_append.mp hnodup).2.2 _ h _ List.mem_cons_self rfl
    exact ⟨(w ++ (m - 1) :: v, false), ⟨by simpa using hsmall, trivial⟩, extend_after _ _ _ hw⟩

private theorem count_succ {a m : ℤ} (ham : a < m) :
    vnArrangementCount 1 (Finset.Ico a (m + 1)).val =
      vnArrangementCount 1 (Finset.Ico a m).val * 2 := by
  have h := (extend_bijOn ham).ncard_eq.symm
  rw [Set.ncard_prod, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_bool] at h
  exact h

end vnArrangementCount_consecutive

/-- **Vn-arrangements of consecutive integers.** For every integer $a$ and every natural number
$t \ge 1$, the set $\{a, a + 1, \dots, a + t - 1\}$ of $t$ consecutive integers has exactly
$2^{t-1}$ vn-arrangements, that is, orderings $(v_1, \dots, v_t)$ of its elements with
$v_{i+1} - v_i \le 1$ for all $i$.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Corollary 5. -/
public theorem vnArrangementCount_consecutive (a : ℤ) (t : ℕ) (ht : 1 ≤ t) :
    vnArrangementCount 1 (Finset.Ico a (a + t)).val = 2 ^ (t - 1) := by
  induction t, ht using Nat.le_induction with
  | base =>
    have h : Finset.Ico a (a + 1) = {a} := by
      ext x
      simp
      omega
    simpa [h] using vnArrangementCount_singleton 1 a
  | succ t ht ih =>
    rw [Nat.cast_succ, ← add_assoc, vnArrangementCount_consecutive.count_succ (by omega), ih]
    rw [show t + 1 - 1 = (t - 1) + 1 by omega, pow_succ]

end MetaMathlibExt
