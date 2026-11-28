/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Non-negative crank generating function (Andrews–Newman / Uncu):
the number of partitions of `N` with crank `≥ 0` equals the alternating
sum of partition numbers at triangular offsets.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.GetD
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Ring

namespace MetaMathlibExt

namespace CrankNonneg

/-- Crank of a partition, using exactly the expression from the `Wanted` entry:
the largest part when no part equals `1`, else the number of parts exceeding
the number of ones minus the number of ones. -/
private def partitionCrank {M : ℕ} (P : Nat.Partition M) : ℤ :=
  if Multiset.count 1 P.parts = 0 then (P.parts.sup : ℤ)
  else (((P.parts.filter (fun i => Multiset.count 1 P.parts < i)).card : ℤ) -
    (Multiset.count 1 P.parts : ℤ))

/-- Number `D(k, M)` of partitions of `M` with crank at most `-k`. -/
private def crankLeCount (k M : ℕ) : ℕ :=
  Fintype.card { P : Nat.Partition M // partitionCrank P ≤ -(k : ℤ) }

/-- Membership condition for `U_k(L)`: at least `ω(π) + 1` parts exceed `ω(π) + k`. -/
private def highPartsCond (k : ℕ) {L : ℕ} (π : Nat.Partition L) : Prop :=
  Multiset.count 1 π.parts + 1 ≤
    (π.parts.filter (fun x => Multiset.count 1 π.parts + k < x)).card

private instance crkDecHigh (k : ℕ) {L : ℕ} :
    DecidablePred (highPartsCond k : Nat.Partition L → Prop) :=
  fun π => by unfold highPartsCond; infer_instance

/-- The non-one parts of a partition, sorted weakly decreasing. -/
private def nonOneParts {n : ℕ} (P : Nat.Partition n) : List ℕ :=
  (P.parts.filter (2 ≤ ·)).sort (· ≥ ·)

/-- Forward list map: add one to each of the first `a` entries, drop entry `a`. -/
private def phiList (a : ℕ) (l : List ℕ) : List ℕ :=
  (List.take a l).map (· + 1) ++ List.drop (a + 1) l

/-- Pivot value for `phiList`. -/
private def phiPivot (a : ℕ) (l : List ℕ) : ℕ := l.getD a 0

/-- Number of entries of `m` exceeding `c`. -/
private def psiCount (c : ℕ) (m : List ℕ) : ℕ :=
  (m.filter (fun x => decide (c < x))).length

/-- Backward list map. -/
private def psiList (c : ℕ) (m : List ℕ) : List ℕ :=
  (List.take (psiCount c m) m).map (· - 1) ++ c :: List.drop (psiCount c m) m

/-- Staircase offset `e(k, m) = (m + 1) * m / 2 + m * (k - 1)`. -/
private def crkE (k m : ℕ) : ℕ := (m + 1) * m / 2 + m * (k - 1)

/-- Alternating partition sum `S(k, M)`. -/
private def crankAltSum (k M : ℕ) : ℤ :=
  ∑ m ∈ Finset.range (M + 1),
    if crkE k m ≤ M then
      (-1 : ℤ) ^ m * (Fintype.card (Nat.Partition (M - crkE k m)) : ℤ)
    else 0

/-! ## Basic crank bounds -/

private theorem crk_lower {M : ℕ} (P : Nat.Partition M) :
    -((Multiset.count 1 P.parts : ℕ) : ℤ) ≤ partitionCrank P := by
  unfold partitionCrank
  split
  · next h => rw [h]; simp
  · next h =>
      have hnn : (0 : ℤ) ≤ (((P.parts.filter
        (fun i => Multiset.count 1 P.parts < i)).card : ℕ) : ℤ) := by
        exact_mod_cast Nat.zero_le _
      omega

private theorem crk_nonneg_of_count_eq_zero {M : ℕ} (P : Nat.Partition M)
    (h : Multiset.count 1 P.parts = 0) : 0 ≤ partitionCrank P := by
  unfold partitionCrank
  split
  · next _ => exact_mod_cast Nat.zero_le _
  · next hne => exact absurd h hne

private theorem crk_le_neg_impl {M k : ℕ} (P : Nat.Partition M) (hk : 1 ≤ k)
    (h : partitionCrank P ≤ -(k : ℤ)) :
    k ≤ Multiset.count 1 P.parts ∧ Multiset.count 1 P.parts ≠ 0 := by
  unfold partitionCrank at h
  split at h
  · next hc =>
      have h1 : (0 : ℤ) ≤ (P.parts.sup : ℤ) := by exact_mod_cast Nat.zero_le _
      omega
  · next hc =>
      have hnn : (0 : ℤ) ≤ (((P.parts.filter
        (fun i => Multiset.count 1 P.parts < i)).card : ℕ) : ℤ) := by
        exact_mod_cast Nat.zero_le _
      refine ⟨by omega, hc⟩

private theorem crk_count_le {M : ℕ} (P : Nat.Partition M) :
    Multiset.count 1 P.parts ≤ M := by
  have h1 : Multiset.count 1 P.parts ≤ Multiset.card P.parts :=
    Multiset.count_le_card 1 P.parts
  have h2 : Multiset.card P.parts ≤ M := by
    calc Multiset.card P.parts = Multiset.card P.parts • 1 := by simp
      _ ≤ P.parts.sum := Multiset.card_nsmul_le_sum (fun x hx => P.parts_pos hx)
      _ = M := P.parts_sum
  omega

private theorem crk_count_eq_zero_of_lt {k M : ℕ} (hk : 1 ≤ k) (hM : M < k) :
    crankLeCount k M = 0 := by
  unfold crankLeCount
  rw [Fintype.card_eq_zero_iff, isEmpty_iff]
  rintro ⟨P, hP⟩
  obtain ⟨hle, -⟩ := crk_le_neg_impl P hk hP
  have hc := crk_count_le P
  omega

/-! ## Adding `k` ones -/

private noncomputable def crkAddOnes (k L : ℕ) :
    Nat.Partition L ≃ { Q : Nat.Partition (L + k) // k ≤ Multiset.count 1 Q.parts } where
  toFun π :=
    ⟨⟨π.parts + Multiset.replicate k 1,
      by
        intro i hi
        rw [Multiset.mem_add] at hi
        rcases hi with h | h
        · exact π.parts_pos h
        · rw [Multiset.mem_replicate] at h
          obtain ⟨-, rfl⟩ := h
          exact Nat.one_pos,
      by
        rw [Multiset.sum_add, Multiset.sum_replicate, π.parts_sum, nsmul_eq_mul,
          mul_one, Nat.cast_id]⟩,
    by
      change k ≤ Multiset.count 1 (π.parts + Multiset.replicate k 1)
      rw [Multiset.count_add, Multiset.count_replicate_self]
      exact Nat.le_add_left k _⟩
  invFun Q :=
    ⟨(Q.1.parts - Multiset.replicate k 1),
      by
        intro i hi
        have hle : Multiset.replicate k 1 ≤ Q.1.parts :=
          Multiset.le_count_iff_replicate_le.mp Q.2
        exact Q.1.parts_pos (Multiset.mem_of_le (Multiset.sub_le_self _ _) hi),
      by
        have hle : Multiset.replicate k 1 ≤ Q.1.parts :=
          Multiset.le_count_iff_replicate_le.mp Q.2
        have hcan := Multiset.sub_add_cancel hle
        have hs := congrArg Multiset.sum hcan
        rw [Multiset.sum_add, Multiset.sum_replicate, Q.1.parts_sum, nsmul_eq_mul,
          mul_one, Nat.cast_id] at hs
        omega⟩
  left_inv π := by
    apply Nat.Partition.ext
    change (π.parts + Multiset.replicate k 1) - Multiset.replicate k 1 = π.parts
    exact Multiset.add_sub_cancel_right
  right_inv Q := by
    apply Subtype.ext
    apply Nat.Partition.ext
    change (Q.1.parts - Multiset.replicate k 1) + Multiset.replicate k 1 = Q.1.parts
    exact Multiset.sub_add_cancel (Multiset.le_count_iff_replicate_le.mp Q.2)

private theorem crkAddOnes_parts (k L : ℕ) (π : Nat.Partition L) :
    (crkAddOnes k L π).1.parts = π.parts + Multiset.replicate k 1 :=
  rfl

private theorem crkAddOnes_omega (k L : ℕ) (π : Nat.Partition L) :
    Multiset.count 1 (crkAddOnes k L π).1.parts = Multiset.count 1 π.parts + k := by
  rw [crkAddOnes_parts, Multiset.count_add, Multiset.count_replicate_self]

/-! ## Crank of the add-ones image -/

private theorem crk_addOnes_filter (k L : ℕ) (hk : 1 ≤ k) (π : Nat.Partition L) :
    ((crkAddOnes k L π).1.parts.filter
      (fun x => Multiset.count 1 π.parts + k < x)).card =
    (π.parts.filter (fun x => Multiset.count 1 π.parts + k < x)).card := by
  rw [crkAddOnes_parts, Multiset.filter_add, Multiset.card_add]
  have hrep : (Multiset.replicate k 1).filter
      (fun x => Multiset.count 1 π.parts + k < x) = 0 := by
    rw [Multiset.filter_eq_nil]
    intro x hx
    rw [Multiset.mem_replicate] at hx
    obtain ⟨-, rfl⟩ := hx
    omega
  rw [hrep, Multiset.card_zero, Nat.add_zero]

private theorem crk_addOnes_crank (k L : ℕ) (hk : 1 ≤ k) (π : Nat.Partition L) :
    partitionCrank (crkAddOnes k L π).1 =
      ((π.parts.filter (fun x => Multiset.count 1 π.parts + k < x)).card : ℤ) -
      ((Multiset.count 1 π.parts + k : ℕ) : ℤ) := by
  have hQ : Multiset.count 1 (crkAddOnes k L π).1.parts =
      Multiset.count 1 π.parts + k :=
    crkAddOnes_omega k L π
  have hne : Multiset.count 1 (crkAddOnes k L π).1.parts ≠ 0 := by omega
  unfold partitionCrank
  split
  · next hcon => exact absurd hcon hne
  · next _ =>
      rw [hQ, crk_addOnes_filter k L hk π]

private theorem crk_not_le_iff_highParts (k L : ℕ) (hk : 1 ≤ k) (π : Nat.Partition L) :
    ¬ partitionCrank (crkAddOnes k L π).1 ≤ -(k : ℤ) ↔ highPartsCond k π := by
  rw [crk_addOnes_crank k L hk π]
  unfold highPartsCond
  constructor <;> intro h <;> omega

/-! ## Recursion first half -/

private def crkEquivLe (k L : ℕ) (hk : 1 ≤ k) :
    { s : { Q : Nat.Partition (L + k) // k ≤ Multiset.count 1 Q.parts } //
      partitionCrank s.1 ≤ -(k : ℤ) } ≃
    { Q : Nat.Partition (L + k) // partitionCrank Q ≤ -(k : ℤ) } :=
  Equiv.subtypeSubtypeEquivSubtype (fun hQ => (crk_le_neg_impl _ hk hQ).1)

private noncomputable def crkEquivHigh (k L : ℕ) (hk : 1 ≤ k) :
    { s : { Q : Nat.Partition (L + k) // k ≤ Multiset.count 1 Q.parts } //
      ¬ partitionCrank s.1 ≤ -(k : ℤ) } ≃
    { π : Nat.Partition L // highPartsCond k π } where
  toFun s :=
    ⟨(crkAddOnes k L).symm s.1,
    by
      have h1 : ((crkAddOnes k L) ((crkAddOnes k L).symm s.1)).1 =
          (s.1 : Nat.Partition (L + k)) :=
        congrArg Subtype.val (Equiv.apply_symm_apply _ _)
      have h2 : ¬ partitionCrank
          ((crkAddOnes k L) ((crkAddOnes k L).symm s.1)).1 ≤ -(k : ℤ) := by
        rw [h1]
        exact s.2
      exact (crk_not_le_iff_highParts k L hk _).mp h2⟩
  invFun t :=
    ⟨(crkAddOnes k L) t.1,
    by
      exact (crk_not_le_iff_highParts k L hk t.1).mpr t.2⟩
  left_inv s := by
    apply Subtype.ext
    exact Equiv.apply_symm_apply _ _
  right_inv t := by
    apply Subtype.ext
    exact Equiv.symm_apply_apply _ _

private theorem crk_add_card_highParts (k L : ℕ) (hk : 1 ≤ k) :
    crankLeCount k (L + k) + Fintype.card { π : Nat.Partition L // highPartsCond k π } =
    Fintype.card (Nat.Partition L) := by
  have h1 := Fintype.card_subtype_compl
    (fun s : { Q : Nat.Partition (L + k) // k ≤ Multiset.count 1 Q.parts } =>
      partitionCrank s.1 ≤ -(k : ℤ))
  have h2 := Fintype.card_subtype_le
    (fun s : { Q : Nat.Partition (L + k) // k ≤ Multiset.count 1 Q.parts } =>
      partitionCrank s.1 ≤ -(k : ℤ))
  have hsplit : Fintype.card { Q : Nat.Partition (L + k) // partitionCrank Q ≤ -(k : ℤ) } +
      Fintype.card { π : Nat.Partition L // highPartsCond k π } =
      Fintype.card (Nat.Partition L) := by
    have h3 := Fintype.card_congr (crkAddOnes k L)
    rw [← Fintype.card_congr (crkEquivLe k L hk),
      ← Fintype.card_congr (crkEquivHigh k L hk)]
    omega
  unfold crankLeCount
  exact hsplit

/-! ## Pair representation -/

private theorem crk_nonOne_mem {n : ℕ} (P : Nat.Partition n) (x : ℕ) :
    x ∈ nonOneParts P ↔ x ∈ P.parts ∧ 2 ≤ x := by
  unfold nonOneParts
  rw [Multiset.mem_sort, Multiset.mem_filter]

private theorem crk_nonOne_sorted {n : ℕ} (P : Nat.Partition n) :
    (nonOneParts P).Pairwise (· ≥ ·) :=
  Multiset.pairwise_sort _ _

private theorem crk_nonOne_ge_two {n : ℕ} (P : Nat.Partition n) :
    ∀ x ∈ nonOneParts P, 2 ≤ x := by
  intro x hx
  exact ((crk_nonOne_mem P x).mp hx).2

private theorem crk_parts_eq_nonOne_add {n : ℕ} (P : Nat.Partition n) :
    P.parts = ((nonOneParts P : Multiset ℕ) + Multiset.replicate (Multiset.count 1 P.parts) 1) := by
  have hsort : ((nonOneParts P : Multiset ℕ)) = P.parts.filter (2 ≤ ·) := by
    rw [nonOneParts, Multiset.sort_eq]
  rw [hsort]
  have hcomp : P.parts.filter (fun x => ¬ 2 ≤ x) =
      Multiset.replicate (Multiset.count 1 P.parts) 1 := by
    have hcongr : P.parts.filter (fun x => ¬ 2 ≤ x) = P.parts.filter (· = 1) := by
      apply Multiset.filter_congr
      intro x hx
      have hpos := P.parts_pos hx
      omega
    rw [hcongr, Multiset.filter_eq']
  conv_lhs => rw [← Multiset.filter_add_not (2 ≤ ·) P.parts]
  rw [hcomp]

private theorem crk_omega_add_sum {n : ℕ} (P : Nat.Partition n) :
    Multiset.count 1 P.parts + (nonOneParts P).sum = n := by
  have h := congrArg Multiset.sum (crk_parts_eq_nonOne_add P)
  rw [Multiset.sum_add, Multiset.sum_coe, Multiset.sum_replicate, nsmul_eq_mul, mul_one,
    Nat.cast_id, P.parts_sum] at h
  omega

private theorem crk_decode {n : ℕ} (l : List ℕ) (hl : l.Pairwise (· ≥ ·))
    (h2 : ∀ x ∈ l, 2 ≤ x) (a : ℕ) (P : Nat.Partition n)
    (hP : P.parts = ((l : Multiset ℕ) + Multiset.replicate a 1)) :
    Multiset.count 1 P.parts = a ∧ nonOneParts P = l := by
  have hcount : Multiset.count 1 ((l : Multiset ℕ)) = 0 := by
    apply Multiset.count_eq_zero.mpr
    intro hmem
    rw [Multiset.mem_coe] at hmem
    have hle := h2 1 hmem
    omega
  have hω : Multiset.count 1 P.parts = a := by
    rw [hP, Multiset.count_add, hcount, Multiset.count_replicate_self, Nat.zero_add]
  refine ⟨hω, ?_⟩
  have hfil : P.parts.filter (2 ≤ ·) = ((l : Multiset ℕ)) := by
    rw [hP, Multiset.filter_add]
    have h1 : ((l : Multiset ℕ)).filter (2 ≤ ·) = ((l : Multiset ℕ)) := by
      rw [Multiset.filter_eq_self]
      intro x hx
      rw [Multiset.mem_coe] at hx
      exact h2 x hx
    have h0 : (Multiset.replicate a 1).filter (2 ≤ ·) = 0 := by
      rw [Multiset.filter_eq_nil]
      intro x hx
      rw [Multiset.mem_replicate] at hx
      obtain ⟨-, rfl⟩ := hx
      omega
    rw [h1, h0, Multiset.add_zero]
  unfold nonOneParts
  rw [hfil, Multiset.coe_sort]
  exact List.mergeSort_eq_self _ hl

private noncomputable def crkMkPartition (L a : ℕ) (l : List ℕ)
    (hpos : ∀ x ∈ l, 1 ≤ x) (hsum : a + l.sum = L) : Nat.Partition L where
  parts := ((l : Multiset ℕ) + Multiset.replicate a 1)
  parts_pos := by
    intro i hi
    rw [Multiset.mem_add] at hi
    rcases hi with h | h
    · rw [Multiset.mem_coe] at h
      have hle := hpos i h
      omega
    · rw [Multiset.mem_replicate] at h
      obtain ⟨-, rfl⟩ := h
      exact Nat.one_pos
  parts_sum := by
    rw [Multiset.sum_add, Multiset.sum_coe, Multiset.sum_replicate, nsmul_eq_mul, mul_one,
      Nat.cast_id]
    omega

private theorem crkMkPartition_parts (L a : ℕ) (l : List ℕ)
    (hpos : ∀ x ∈ l, 1 ≤ x) (hsum : a + l.sum = L) :
    (crkMkPartition L a l hpos hsum).parts = ((l : Multiset ℕ) + Multiset.replicate a 1) :=
  rfl

private theorem crk_filter_threshold {n : ℕ} (P : Nat.Partition n) (t : ℕ) (ht : 1 ≤ t) :
    (P.parts.filter (fun x => t < x)).card =
    ((nonOneParts P).filter (fun x => t < x)).length := by
  rw [crk_parts_eq_nonOne_add P, Multiset.filter_add, Multiset.card_add]
  have hrep : (Multiset.replicate (Multiset.count 1 P.parts) 1).filter
      (fun x => t < x) = 0 := by
    rw [Multiset.filter_eq_nil]
    intro x hx
    rw [Multiset.mem_replicate] at hx
    obtain ⟨-, rfl⟩ := hx
    omega
  rw [hrep, Multiset.card_zero, Nat.add_zero, Multiset.filter_coe, Multiset.coe_card]

/-! ## Threshold lemmas for weakly decreasing lists -/

private theorem crk_filter_split {l l₁ l₂ : List ℕ} (t : ℕ)
    (h : l = l₁ ++ l₂) (h₁ : ∀ x ∈ l₁, t < x) (h₂ : ∀ x ∈ l₂, x ≤ t) :
    (l.filter (fun x => decide (t < x))).length = l₁.length := by
  rw [h, List.filter_append,
    List.filter_eq_self.mpr (fun a ha => by simpa using h₁ a ha),
    List.filter_eq_nil_iff.mpr (fun a ha hcon => by
      have hlt : t < a := of_decide_eq_true hcon
      have hle := h₂ a ha
      omega),
    List.append_nil]

private theorem crk_sorted_filter_spec (l : List ℕ) (hl : l.Pairwise (· ≥ ·)) (t : ℕ) :
    (l.filter (fun x => decide (t < x))).length ≤ l.length ∧
    (∀ x ∈ List.take (l.filter (fun x => decide (t < x))).length l, t < x) ∧
    (∀ x ∈ List.drop (l.filter (fun x => decide (t < x))).length l, x ≤ t) := by
  have hempty_of_le : ∀ (hd : ℕ) (tl : List ℕ),
      (∀ y ∈ tl, hd ≥ y) → hd ≤ t →
      ((hd :: tl).filter (fun x => decide (t < x))) = [] := by
    intro hd tl hhead hle
    rw [List.filter_eq_nil_iff]
    intro y hy hcon
    have hlt : t < y := of_decide_eq_true hcon
    rw [List.mem_cons] at hy
    rcases hy with rfl | hy
    · omega
    · have hyhd := hhead y hy
      omega
  have htake : ∀ (l : List ℕ), l.Pairwise (· ≥ ·) →
      ∀ x ∈ List.take (l.filter (fun x => decide (t < x))).length l, t < x := by
    intro l
    induction l with
    | nil =>
      intro _ x hx
      simp at hx
    | cons hd tl ih =>
      intro hl x hx
      rw [List.pairwise_cons] at hl
      obtain ⟨hhead, htail⟩ := hl
      by_cases hhd : t < hd
      · have hfil : ((hd :: tl).filter (fun x => decide (t < x))).length =
            (tl.filter (fun x => decide (t < x))).length + 1 := by
          rw [List.filter_cons_of_pos (by simpa using hhd), List.length_cons]
        rw [hfil, List.take_succ_cons, List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact hhd
        · exact ih htail x hx
      · have hle : hd ≤ t := le_of_not_gt hhd
        have hempty := hempty_of_le hd tl hhead hle
        have hb0 : ((hd :: tl).filter (fun x => decide (t < x))).length = 0 :=
          List.length_eq_zero_iff.mpr hempty
        rw [hb0] at hx
        simp at hx
  have hdrop : ∀ (l : List ℕ), l.Pairwise (· ≥ ·) →
      ∀ x ∈ List.drop (l.filter (fun x => decide (t < x))).length l, x ≤ t := by
    intro l
    induction l with
    | nil =>
      intro _ x hx
      simp at hx
    | cons hd tl ih =>
      intro hl x hx
      rw [List.pairwise_cons] at hl
      obtain ⟨hhead, htail⟩ := hl
      by_cases hhd : t < hd
      · have hfil : ((hd :: tl).filter (fun x => decide (t < x))).length =
            (tl.filter (fun x => decide (t < x))).length + 1 := by
          rw [List.filter_cons_of_pos (by simpa using hhd), List.length_cons]
        have hdrop : List.drop
            ((tl.filter (fun x => decide (t < x))).length + 1) (hd :: tl) =
            List.drop (tl.filter (fun x => decide (t < x))).length tl :=
          rfl
        rw [hfil, hdrop] at hx
        exact ih htail x hx
      · have hle : hd ≤ t := le_of_not_gt hhd
        have hempty := hempty_of_le hd tl hhead hle
        have hb0 : ((hd :: tl).filter (fun x => decide (t < x))).length = 0 :=
          List.length_eq_zero_iff.mpr hempty
        rw [hb0, List.drop_zero, List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact hle
        · have hle2 : x ≤ hd := hhead x hx
          omega
  exact ⟨List.length_filter_le _ _, htake l hl, hdrop l hl⟩

private theorem crk_mem_filter_iff (l : List ℕ) (hl : l.Pairwise (· ≥ ·)) (t n : ℕ)
    (h : n < l.length) :
    n + 1 ≤ (l.filter (fun x => decide (t < x))).length ↔ t < l[n] := by
  have hspec := crk_sorted_filter_spec l hl t
  set b := (l.filter (fun x => decide (t < x))).length
  constructor
  · intro hle
    have hblen : n < (List.take b l).length := by
      rw [List.length_take]
      omega
    have hmem := List.getElem_mem hblen
    have hlt := hspec.2.1 _ hmem
    rw [List.getElem_take] at hlt
    exact hlt
  · intro hlt
    by_contra hcon
    have hbn : b ≤ n := by omega
    have hlen : n - b < (List.drop b l).length := by
      rw [List.length_drop]
      omega
    have hmem := List.getElem_mem hlen
    have hle := hspec.2.2 _ hmem
    rw [List.getElem_drop] at hle
    simp only [Nat.add_sub_cancel' hbn] at hle
    exact (not_lt.mpr hle) hlt

/-! ## Forward list map -/

private theorem crk_sum_map_succ (t : List ℕ) :
    (t.map (· + 1)).sum = t.sum + t.length := by
  induction t with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
    omega

private theorem crk_phi_sorted (a : ℕ) (l : List ℕ)
    (hl : l.Pairwise (· ≥ ·)) (hlen : a < l.length) :
    (phiList a l).Pairwise (· ≥ ·) := by
  have hpre : ((List.take a l).map (· + 1)).Pairwise (· ≥ ·) := by
    rw [List.pairwise_map]
    exact (hl.sublist (List.take_sublist a l)).imp (fun h => by omega)
  have hsuf : (List.drop (a + 1) l).Pairwise (· ≥ ·) :=
    hl.sublist (List.drop_sublist (a + 1) l)
  have hacross : ∀ x ∈ (List.take a l).map (· + 1),
      ∀ y ∈ List.drop (a + 1) l, x ≥ y := by
    intro x hx y hy
    rw [List.mem_map] at hx
    obtain ⟨u, hu, rfl⟩ := hx
    rw [List.mem_iff_getElem] at hu hy
    obtain ⟨i, hi, hui⟩ := hu
    obtain ⟨j, hj, hyj⟩ := hy
    rw [List.getElem_take] at hui
    rw [List.getElem_drop] at hyj
    have hi_len : i < l.length := by
      have hii := hi
      rw [List.length_take] at hii
      omega
    have hj_len : (a + 1) + j < l.length := by
      have hjj := hj
      rw [List.length_drop] at hjj
      omega
    have hia : i < a := by
      have hii := hi
      rw [List.length_take] at hii
      omega
    have hle := (List.pairwise_iff_getElem.mp hl) i ((a + 1) + j) hi_len hj_len
      (by omega)
    omega
  rw [phiList, List.pairwise_append]
  exact ⟨hpre, hsuf, hacross⟩

private theorem crk_phi_ge_two (a : ℕ) (l : List ℕ)
    (h2 : ∀ x ∈ l, 2 ≤ x) :
    ∀ x ∈ phiList a l, 2 ≤ x := by
  intro x hx
  rw [phiList, List.mem_append] at hx
  rcases hx with hx | hx
  · rw [List.mem_map] at hx
    obtain ⟨u, hu, rfl⟩ := hx
    rw [List.mem_iff_getElem] at hu
    obtain ⟨i, hi, hui⟩ := hu
    rw [List.getElem_take] at hui
    have hii : i < l.length := by
      have h3 := hi
      rw [List.length_take] at h3
      omega
    have hu2 : 2 ≤ u := hui ▸ h2 _ (List.getElem_mem hii)
    omega
  · rw [List.mem_iff_getElem] at hx
    obtain ⟨j, hj, hyj⟩ := hx
    rw [List.getElem_drop] at hyj
    rw [← hyj]
    exact h2 _ (List.getElem_mem (by
      have hjj := hj
      rw [List.length_drop] at hjj
      omega))

private theorem crk_phi_sum (a : ℕ) (l : List ℕ)
    (hlen : a < l.length) :
    phiPivot a l + (phiList a l).sum = a + l.sum := by
  have hpiv : phiPivot a l = l[a]'hlen := List.getD_eq_getElem _ _ hlen
  have hdrop : List.drop a l = l[a]'hlen :: List.drop (a + 1) l :=
    List.drop_eq_getElem_cons hlen
  have htsum : (List.take a l).sum + (List.drop a l).sum = l.sum := by
    rw [← List.sum_append, List.take_append_drop]
  have hmap : ((List.take a l).map (· + 1)).sum = (List.take a l).sum + a := by
    rw [crk_sum_map_succ]
    have hlen2 : (List.take a l).length = a := by
      rw [List.length_take, Nat.min_eq_left (le_of_lt hlen)]
    rw [hlen2]
  rw [phiList, hpiv, List.sum_append, hmap]
  rw [hdrop, List.sum_cons] at htsum
  omega

private theorem crk_phi_filter (a : ℕ) (l : List ℕ)
    (hl : l.Pairwise (· ≥ ·)) (hlen : a < l.length) :
    ((phiList a l).filter (fun x => decide (phiPivot a l < x))).length = a := by
  have hpiv : phiPivot a l = l[a]'hlen := List.getD_eq_getElem _ _ hlen
  have hsplit : phiList a l =
      (List.take a l).map (· + 1) ++ List.drop (a + 1) l := rfl
  refine (crk_filter_split (phiPivot a l) hsplit ?_ ?_).trans ?_
  · intro x hx
    rw [hpiv]
    rw [List.mem_map] at hx
    obtain ⟨u, hu, rfl⟩ := hx
    rw [List.mem_iff_getElem] at hu
    obtain ⟨i, hi, hui⟩ := hu
    rw [List.getElem_take] at hui
    have hi_len : i < l.length := by
      have hii := hi
      rw [List.length_take] at hii
      omega
    have hia : i < a := by
      have hii := hi
      rw [List.length_take] at hii
      omega
    have hle := (List.pairwise_iff_getElem.mp hl) i a hi_len hlen hia
    omega
  · intro y hy
    rw [hpiv]
    rw [List.mem_iff_getElem] at hy
    obtain ⟨j, hj, hyj⟩ := hy
    rw [List.getElem_drop] at hyj
    have hj_len : (a + 1) + j < l.length := by
      have hjj := hj
      rw [List.length_drop] at hjj
      omega
    have hle := (List.pairwise_iff_getElem.mp hl) a ((a + 1) + j) hlen hj_len
      (by omega)
    omega
  · rw [List.length_map, List.length_take, Nat.min_eq_left (le_of_lt hlen)]

private theorem crk_phi_pivot_big (k a : ℕ) (l : List ℕ)
    (hlen : a < l.length) (hbig : a + k < l[a]) :
    a + k + 1 ≤ phiPivot a l := by
  unfold phiPivot
  rw [List.getD_eq_getElem _ _ hlen]
  exact hbig

/-! ## Backward list map -/

private theorem crk_psi_sorted (c : ℕ) (m : List ℕ)
    (hm : m.Pairwise (· ≥ ·)) :
    (psiList c m).Pairwise (· ≥ ·) := by
  have hspec := crk_sorted_filter_spec m hm c
  have htake : ∀ x ∈ List.take (psiCount c m) m, c < x := hspec.2.1
  have hdrop : ∀ x ∈ List.drop (psiCount c m) m, x ≤ c := hspec.2.2
  have hpsplit : psiList c m =
      (List.take (psiCount c m) m).map (· - 1) ++ c :: List.drop (psiCount c m) m := rfl
  have hpre : ((List.take (psiCount c m) m).map (· - 1)).Pairwise (· ≥ ·) := by
    rw [List.pairwise_map]
    exact (hm.sublist (List.take_sublist _ _)).imp (fun h => by omega)
  have hsuf : (c :: List.drop (psiCount c m) m).Pairwise (· ≥ ·) := by
    rw [List.pairwise_cons]
    exact ⟨fun y hy => hdrop y hy, hm.sublist (List.drop_sublist _ _)⟩
  have hacross : ∀ x ∈ (List.take (psiCount c m) m).map (· - 1),
      ∀ y ∈ c :: List.drop (psiCount c m) m, x ≥ y := by
    intro x hx y hy
    rw [List.mem_map] at hx
    obtain ⟨u, hu, rfl⟩ := hx
    rw [List.mem_cons] at hy
    rcases hy with rfl | hy
    · have hu2 := htake u hu
      omega
    · have hu2 := htake u hu
      have hy2 := hdrop y hy
      omega
  rw [hpsplit, List.pairwise_append]
  exact ⟨hpre, hsuf, hacross⟩

private theorem crk_psi_ge_two (k c : ℕ) (m : List ℕ) (hk : 1 ≤ k)
    (hm : m.Pairwise (· ≥ ·)) (h2 : ∀ x ∈ m, 2 ≤ x)
    (hbig : psiCount c m + k + 1 ≤ c) :
    ∀ x ∈ psiList c m, 2 ≤ x := by
  have hspec := crk_sorted_filter_spec m hm c
  have htake : ∀ x ∈ List.take (psiCount c m) m, c < x := hspec.2.1
  have hpsplit : psiList c m =
      (List.take (psiCount c m) m).map (· - 1) ++ c :: List.drop (psiCount c m) m := rfl
  have hmem_drop : ∀ y ∈ List.drop (psiCount c m) m, y ∈ m := by
    intro y hy
    rw [List.mem_iff_getElem] at hy
    obtain ⟨j, hj, hyj⟩ := hy
    rw [List.getElem_drop] at hyj
    rw [← hyj]
    exact List.getElem_mem (by
      have hjj := hj
      rw [List.length_drop] at hjj
      omega)
  intro x hx
  rw [hpsplit, List.mem_append, List.mem_cons] at hx
  rcases hx with hx | rfl | hx
  · rw [List.mem_map] at hx
    obtain ⟨u, hu, rfl⟩ := hx
    have hu2 := htake u hu
    omega
  · omega
  · exact h2 x (hmem_drop x hx)

private theorem crk_psi_sum (c : ℕ) (m : List ℕ)
    (h2 : ∀ x ∈ m, 2 ≤ x) :
    psiCount c m + (psiList c m).sum = c + m.sum := by
  have hpsplit : psiList c m =
      (List.take (psiCount c m) m).map (· - 1) ++ c :: List.drop (psiCount c m) m := rfl
  have hbdef : psiCount c m = (m.filter (fun x => decide (c < x))).length := rfl
  have hble : psiCount c m ≤ m.length := by
    rw [hbdef]
    exact List.length_filter_le _ _
  have hmem_take : ∀ u ∈ List.take (psiCount c m) m, u ∈ m := by
    intro u hu
    rw [List.mem_iff_getElem] at hu
    obtain ⟨i, hi, hui⟩ := hu
    rw [List.getElem_take] at hui
    rw [← hui]
    exact List.getElem_mem (by
      have hii := hi
      rw [List.length_take] at hii
      omega)
  have htsum : (List.take (psiCount c m) m).sum + (List.drop (psiCount c m) m).sum
      = m.sum := by
    rw [← List.sum_append, List.take_append_drop]
  have hmap : ((List.take (psiCount c m) m).map (· - 1)).sum + psiCount c m
      = (List.take (psiCount c m) m).sum := by
    have hround : ((List.take (psiCount c m) m).map (· - 1)).map (· + 1)
        = List.take (psiCount c m) m := by
      rw [List.map_map]
      have hcongr : (List.take (psiCount c m) m).map ((· + 1) ∘ (· - 1))
          = (List.take (psiCount c m) m).map id :=
        List.map_congr_left (fun u hu => by
          have hu2 : 2 ≤ u := h2 u (hmem_take u hu)
          have h1 : 1 ≤ u := by omega
          exact Nat.sub_add_cancel h1)
      rw [hcongr, List.map_id]
    have hsum := congrArg List.sum hround
    rw [crk_sum_map_succ, List.length_map] at hsum
    have htake_len : (List.take (psiCount c m) m).length = psiCount c m := by
      rw [List.length_take, Nat.min_eq_left hble]
    rw [htake_len] at hsum
    exact hsum
  rw [hpsplit, List.sum_append, List.sum_cons]
  omega

private theorem crk_psi_length (c : ℕ) (m : List ℕ)
    (hm : m.Pairwise (· ≥ ·)) :
    psiCount c m < (psiList c m).length := by
  have hspec := crk_sorted_filter_spec m hm c
  have hbdef : psiCount c m = (m.filter (fun x => decide (c < x))).length := rfl
  have hpsplit : psiList c m =
      (List.take (psiCount c m) m).map (· - 1) ++ c :: List.drop (psiCount c m) m := rfl
  rw [hpsplit, List.length_append, List.length_map, List.length_cons, hbdef]
  have htake_len : (List.take (m.filter (fun x => decide (c < x))).length m).length
      = (m.filter (fun x => decide (c < x))).length := by
    rw [List.length_take, Nat.min_eq_left hspec.1]
  rw [htake_len]
  omega

private theorem crk_psi_pivot (c : ℕ) (m : List ℕ)
    (hm : m.Pairwise (· ≥ ·)) :
    (psiList c m).getD (psiCount c m) 0 = c := by
  have hspec := crk_sorted_filter_spec m hm c
  have hbdef : psiCount c m = (m.filter (fun x => decide (c < x))).length := rfl
  have hble : psiCount c m ≤ m.length := by
    rw [hbdef]
    exact hspec.1
  have hpsplit : psiList c m =
      (List.take (psiCount c m) m).map (· - 1) ++ c :: List.drop (psiCount c m) m := rfl
  have htake_len : (List.take (psiCount c m) m).length = psiCount c m := by
    rw [List.length_take, Nat.min_eq_left hble]
  have hmap_len : ((List.take (psiCount c m) m).map (· - 1)).length
      = psiCount c m := by
    rw [List.length_map]
    exact htake_len
  have hlen : psiCount c m < (psiList c m).length :=
    crk_psi_length c m hm
  have hget : (psiList c m).getD (psiCount c m) 0
      = (psiList c m)[psiCount c m]'hlen := List.getD_eq_getElem _ _ hlen
  rw [hget]
  simp only [hpsplit, List.getElem_append_right (le_of_eq hmap_len), hmap_len,
    Nat.sub_self, List.getElem_cons_zero]

/-! ## List maps are inverse -/

private theorem crk_psi_phi (a : ℕ) (l : List ℕ)
    (hl : l.Pairwise (· ≥ ·)) (hlen : a < l.length) :
    psiCount (phiPivot a l) (phiList a l) = a ∧
    psiList (phiPivot a l) (phiList a l) = l := by
  have hpiv : phiPivot a l = l[a]'hlen := List.getD_eq_getElem _ _ hlen
  have hcount1 : psiCount (phiPivot a l) (phiList a l) = a :=
    crk_phi_filter a l hl hlen
  refine ⟨hcount1, ?_⟩
  have hsplit_phi : phiList a l =
      (List.take a l).map (· + 1) ++ List.drop (a + 1) l := rfl
  have hmaplen : ((List.take a l).map (· + 1)).length = a := by
    rw [List.length_map, List.length_take, Nat.min_eq_left (le_of_lt hlen)]
  have htake : List.take a (phiList a l) = (List.take a l).map (· + 1) := by
    rw [hsplit_phi]
    exact List.take_left' hmaplen
  have hdrop : List.drop a (phiList a l) = List.drop (a + 1) l := by
    rw [hsplit_phi]
    exact List.drop_left' hmaplen
  have hmapback : ((List.take a l).map (· + 1)).map (· - 1) = List.take a l := by
    rw [List.map_map]
    exact List.map_id'' (fun x => Nat.add_sub_cancel x 1) _
  have hda : List.drop a l = l[a]'hlen :: List.drop (a + 1) l :=
    List.drop_eq_getElem_cons hlen
  have hpsplit : psiList (phiPivot a l) (phiList a l) =
      (List.take (psiCount (phiPivot a l) (phiList a l)) (phiList a l)).map (· - 1) ++
      phiPivot a l ::
        List.drop (psiCount (phiPivot a l) (phiList a l)) (phiList a l) := rfl
  rw [hpsplit, hcount1, hpiv, htake, hdrop, hmapback, ← hda, List.take_append_drop]

private theorem crk_phi_psi (c : ℕ) (m : List ℕ)
    (hm : m.Pairwise (· ≥ ·)) :
    (psiList c m).getD (psiCount c m) 0 = c ∧
    phiList (psiCount c m) (psiList c m) = m := by
  have hspec := crk_sorted_filter_spec m hm c
  have htake : ∀ x ∈ List.take (psiCount c m) m, c < x := hspec.2.1
  have hble : psiCount c m ≤ m.length := hspec.1
  have hpsplit : psiList c m =
      (List.take (psiCount c m) m).map (· - 1) ++ c :: List.drop (psiCount c m) m := rfl
  have hmaplen : ((List.take (psiCount c m) m).map (· - 1)).length
      = psiCount c m := by
    rw [List.length_map, List.length_take, Nat.min_eq_left hble]
  have hget : (psiList c m).getD (psiCount c m) 0 = c :=
    crk_psi_pivot c m hm
  refine ⟨hget, ?_⟩
  have htake2 : List.take (psiCount c m) (psiList c m)
      = (List.take (psiCount c m) m).map (· - 1) := by
    rw [hpsplit]
    exact List.take_left' hmaplen
  have hdrop2 : List.drop (psiCount c m + 1) (psiList c m)
      = List.drop (psiCount c m) m := by
    rw [hpsplit]
    have heq : psiCount c m + 1
        = ((List.take (psiCount c m) m).map (· - 1)).length + 1 := by
      rw [hmaplen]
    rw [heq, List.drop_length_add_append]
    exact rfl
  have hround : ((List.take (psiCount c m) m).map (· - 1)).map (· + 1)
      = List.take (psiCount c m) m := by
    rw [List.map_map]
    have hcongr : (List.take (psiCount c m) m).map ((· + 1) ∘ (· - 1))
        = (List.take (psiCount c m) m).map id :=
      List.map_congr_left (fun u hu => by
        have huc := htake u hu
        have h1 : 1 ≤ u := by omega
        exact Nat.sub_add_cancel h1)
    rw [hcongr, List.map_id]
  have hphsplit : phiList (psiCount c m) (psiList c m) =
      (List.take (psiCount c m) (psiList c m)).map (· + 1) ++
      List.drop (psiCount c m + 1) (psiList c m) := rfl
  rw [hphsplit, htake2, hdrop2, hround, List.take_append_drop]

/-! ## Lifting to partitions -/

private theorem crk_phi_index (k L : ℕ) (hk : 1 ≤ k) (π : Nat.Partition L)
    (hπ : highPartsCond k π) :
    Multiset.count 1 π.parts < (nonOneParts π).length ∧
    Multiset.count 1 π.parts + k
      < phiPivot (Multiset.count 1 π.parts) (nonOneParts π) := by
  have hle1 : Multiset.count 1 π.parts + 1 ≤
      ((nonOneParts π).filter
        (fun x => decide (Multiset.count 1 π.parts + k < x))).length := by
    have hπ' := hπ
    unfold highPartsCond at hπ'
    rwa [crk_filter_threshold π (Multiset.count 1 π.parts + k) (by omega)] at hπ'
  have hlen : Multiset.count 1 π.parts < (nonOneParts π).length := by
    have hb := (crk_sorted_filter_spec (nonOneParts π) (crk_nonOne_sorted π)
      (Multiset.count 1 π.parts + k)).1
    omega
  refine ⟨hlen, ?_⟩
  have hpiv : phiPivot (Multiset.count 1 π.parts) (nonOneParts π)
      = (nonOneParts π)[Multiset.count 1 π.parts]'hlen :=
    List.getD_eq_getElem _ _ hlen
  rw [hpiv]
  have hiff := crk_mem_filter_iff (nonOneParts π) (crk_nonOne_sorted π)
    (Multiset.count 1 π.parts + k) (Multiset.count 1 π.parts) hlen
  exact hiff.mp hle1

private noncomputable def crkPhiFun (k L : ℕ) (hk : 1 ≤ k) (π : Nat.Partition L)
    (hπ : highPartsCond k π) : Nat.Partition L :=
  crkMkPartition L (phiPivot (Multiset.count 1 π.parts) (nonOneParts π))
    (phiList (Multiset.count 1 π.parts) (nonOneParts π))
    (fun x hx => by
      have hge := crk_phi_ge_two _ _ (crk_nonOne_ge_two π) x hx
      omega)
    (by
      have hlen := (crk_phi_index k L hk π hπ).1
      rw [crk_phi_sum _ _ hlen]
      exact crk_omega_add_sum π)

private theorem crkPhiFun_mem (k L : ℕ) (hk : 1 ≤ k) (π : Nat.Partition L)
    (hπ : highPartsCond k π) :
    partitionCrank (crkPhiFun k L hk π hπ) ≤ -(((k + 1 : ℕ) : ℕ) : ℤ) := by
  obtain ⟨hlen, hbig⟩ := crk_phi_index k L hk π hπ
  have hl_sorted := crk_nonOne_sorted π
  have h2_sorted := crk_nonOne_ge_two π
  have hpiv : phiPivot (Multiset.count 1 π.parts) (nonOneParts π)
      = (nonOneParts π)[Multiset.count 1 π.parts]'hlen :=
    List.getD_eq_getElem _ _ hlen
  have hbig' : Multiset.count 1 π.parts + k
      < (nonOneParts π)[Multiset.count 1 π.parts]'hlen := by
    rw [← hpiv]
    exact hbig
  have hparts : (crkPhiFun k L hk π hπ).parts
      = ((phiList (Multiset.count 1 π.parts) (nonOneParts π) : Multiset ℕ)
        + Multiset.replicate
          (phiPivot (Multiset.count 1 π.parts) (nonOneParts π)) 1) := by
    unfold crkPhiFun
    rw [crkMkPartition_parts]
  have hdec := crk_decode (phiList (Multiset.count 1 π.parts) (nonOneParts π))
    (crk_phi_sorted _ _ hl_sorted hlen) (crk_phi_ge_two _ _ h2_sorted)
    (phiPivot (Multiset.count 1 π.parts) (nonOneParts π)) _ hparts
  have hω := hdec.1
  have hnon := hdec.2
  have hpivbig := crk_phi_pivot_big k _ _ hlen hbig'
  have hωpos : 1 ≤ phiPivot (Multiset.count 1 π.parts) (nonOneParts π) := by
    omega
  have hne : Multiset.count 1 (crkPhiFun k L hk π hπ).parts ≠ 0 := by omega
  have hcrank : partitionCrank (crkPhiFun k L hk π hπ)
      = ((Multiset.count 1 π.parts : ℕ) : ℤ)
        - ((phiPivot (Multiset.count 1 π.parts) (nonOneParts π) : ℕ) : ℤ) := by
    unfold partitionCrank
    split
    · next hcon => exact absurd hcon hne
    · next _ =>
        rw [hω, crk_filter_threshold _ _ hωpos, hnon,
          crk_phi_filter _ _ hl_sorted hlen]
  rw [hcrank]
  omega

private noncomputable def crkPhi (k L : ℕ) (hk : 1 ≤ k)
    (π : { π : Nat.Partition L // highPartsCond k π }) :
    { ν : Nat.Partition L // partitionCrank ν ≤ -(((k + 1 : ℕ) : ℕ) : ℤ) } :=
  ⟨crkPhiFun k L hk π.1 π.2, crkPhiFun_mem k L hk π.1 π.2⟩

private theorem crk_psi_index (k L : ℕ) (hk : 1 ≤ k) (ν : Nat.Partition L)
    (hν : partitionCrank ν ≤ -(((k + 1 : ℕ) : ℕ) : ℤ)) :
    Multiset.count 1 ν.parts ≠ 0 ∧
    psiCount (Multiset.count 1 ν.parts) (nonOneParts ν) + k + 1
      ≤ Multiset.count 1 ν.parts := by
  have hN1 := crk_le_neg_impl ν (by omega : 1 ≤ k + 1) hν
  obtain ⟨-, hne⟩ := hN1
  refine ⟨hne, ?_⟩
  have hc1 : 1 ≤ Multiset.count 1 ν.parts := by omega
  have hfil : (ν.parts.filter (fun x => Multiset.count 1 ν.parts < x)).card
      = psiCount (Multiset.count 1 ν.parts) (nonOneParts ν) :=
    crk_filter_threshold ν _ hc1
  unfold partitionCrank at hν
  split at hν
  · next hcon => exact absurd hcon hne
  · next _ =>
      rw [hfil] at hν
      omega

private noncomputable def crkPsiFun (k L : ℕ) (hk : 1 ≤ k) (ν : Nat.Partition L)
    (hν : partitionCrank ν ≤ -(((k + 1 : ℕ) : ℕ) : ℤ)) : Nat.Partition L :=
  crkMkPartition L (psiCount (Multiset.count 1 ν.parts) (nonOneParts ν))
    (psiList (Multiset.count 1 ν.parts) (nonOneParts ν))
    (fun x hx => by
      have hbig2 := (crk_psi_index k L hk ν hν).2
      have hge := crk_psi_ge_two k _ _ hk (crk_nonOne_sorted ν)
        (crk_nonOne_ge_two ν) hbig2 x hx
      omega)
    (by
      have hbig2 := (crk_psi_index k L hk ν hν).2
      have hsum : psiCount (Multiset.count 1 ν.parts) (nonOneParts ν)
          + (psiList (Multiset.count 1 ν.parts) (nonOneParts ν)).sum
          = Multiset.count 1 ν.parts + (nonOneParts ν).sum :=
        crk_psi_sum _ _ (crk_nonOne_ge_two ν)
      have hωsum := crk_omega_add_sum ν
      omega)

private theorem crkPsiFun_mem (k L : ℕ) (hk : 1 ≤ k) (ν : Nat.Partition L)
    (hν : partitionCrank ν ≤ -(((k + 1 : ℕ) : ℕ) : ℤ)) :
    highPartsCond k (crkPsiFun k L hk ν hν) := by
  obtain ⟨-, hbig⟩ := crk_psi_index k L hk ν hν
  have hl_sorted := crk_nonOne_sorted ν
  have hsorted' :=
    crk_psi_sorted (Multiset.count 1 ν.parts) (nonOneParts ν) hl_sorted
  have hparts : (crkPsiFun k L hk ν hν).parts
      = (((psiList (Multiset.count 1 ν.parts) (nonOneParts ν) : Multiset ℕ))
        + Multiset.replicate
          (psiCount (Multiset.count 1 ν.parts) (nonOneParts ν)) 1) := by
    unfold crkPsiFun
    rw [crkMkPartition_parts]
  have hdec := crk_decode (psiList (Multiset.count 1 ν.parts) (nonOneParts ν))
    hsorted'
    (crk_psi_ge_two k _ _ hk hl_sorted (crk_nonOne_ge_two ν) hbig)
    (psiCount (Multiset.count 1 ν.parts) (nonOneParts ν)) _ hparts
  have hω := hdec.1
  have hnon := hdec.2
  have hlen_b : psiCount (Multiset.count 1 ν.parts) (nonOneParts ν)
      < (psiList (Multiset.count 1 ν.parts) (nonOneParts ν)).length :=
    crk_psi_length (Multiset.count 1 ν.parts) (nonOneParts ν) hl_sorted
  have hpivget : (psiList (Multiset.count 1 ν.parts) (nonOneParts ν))[
      psiCount (Multiset.count 1 ν.parts) (nonOneParts ν)]'hlen_b
      = Multiset.count 1 ν.parts := by
    have hpiv : (psiList (Multiset.count 1 ν.parts) (nonOneParts ν)).getD
        (psiCount (Multiset.count 1 ν.parts) (nonOneParts ν)) 0
        = Multiset.count 1 ν.parts :=
      crk_psi_pivot (Multiset.count 1 ν.parts) (nonOneParts ν) hl_sorted
    rwa [List.getD_eq_getElem _ _ hlen_b] at hpiv
  have hlt : psiCount (Multiset.count 1 ν.parts) (nonOneParts ν) + k
      < (psiList (Multiset.count 1 ν.parts) (nonOneParts ν))[
        psiCount (Multiset.count 1 ν.parts) (nonOneParts ν)]'hlen_b := by
    rw [hpivget]
    omega
  have hiff := crk_mem_filter_iff
    (psiList (Multiset.count 1 ν.parts) (nonOneParts ν)) hsorted'
    (psiCount (Multiset.count 1 ν.parts) (nonOneParts ν) + k)
    (psiCount (Multiset.count 1 ν.parts) (nonOneParts ν)) hlen_b
  unfold highPartsCond
  rw [hω]
  have h1k : 1 ≤ psiCount (Multiset.count 1 ν.parts) (nonOneParts ν) + k := by
    omega
  rw [crk_filter_threshold _ _ h1k, hnon]
  exact hiff.mpr hlt

private noncomputable def crkPsi (k L : ℕ) (hk : 1 ≤ k)
    (ν : { ν : Nat.Partition L // partitionCrank ν ≤ -(((k + 1 : ℕ) : ℕ) : ℤ) }) :
    { π : Nat.Partition L // highPartsCond k π } :=
  ⟨crkPsiFun k L hk ν.1 ν.2, crkPsiFun_mem k L hk ν.1 ν.2⟩

private theorem crk_phi_mem (k L : ℕ) (hk : 1 ≤ k) (π : Nat.Partition L)
    (hπ : highPartsCond k π) :
    Multiset.count 1 π.parts < (nonOneParts π).length ∧
    Multiset.count 1 π.parts + k <
      phiPivot (Multiset.count 1 π.parts) (nonOneParts π) ∧
    partitionCrank (crkPhi k L hk ⟨π, hπ⟩).1 ≤ -(((k + 1 : ℕ) : ℕ) : ℤ) := by
  obtain ⟨hlen, hbig⟩ := crk_phi_index k L hk π hπ
  exact ⟨hlen, hbig, crkPhiFun_mem k L hk π hπ⟩

private theorem crk_psi_mem (k L : ℕ) (hk : 1 ≤ k) (ν : Nat.Partition L)
    (hν : partitionCrank ν ≤ -(((k + 1 : ℕ) : ℕ) : ℤ)) :
    let c := Multiset.count 1 ν.parts
    let m := nonOneParts ν
    c ≠ 0 ∧ psiCount c m + k + 1 ≤ c ∧ highPartsCond k (crkPsi k L hk ⟨ν, hν⟩).1 := by
  obtain ⟨hne, hbig⟩ := crk_psi_index k L hk ν hν
  exact ⟨hne, hbig, crkPsiFun_mem k L hk ν hν⟩

/-! ## Card equality -/

private theorem crk_fun_left_inv (k L : ℕ) (hk : 1 ≤ k) (π : Nat.Partition L)
    (hπ : highPartsCond k π) :
    crkPsiFun k L hk (crkPhiFun k L hk π hπ)
      (crkPhiFun_mem k L hk π hπ) = π := by
  obtain ⟨hlen, -⟩ := crk_phi_index k L hk π hπ
  have hl_sorted := crk_nonOne_sorted π
  have hpartsΦ : (crkPhiFun k L hk π hπ).parts
      = ((phiList (Multiset.count 1 π.parts) (nonOneParts π) : Multiset ℕ)
        + Multiset.replicate
          (phiPivot (Multiset.count 1 π.parts) (nonOneParts π)) 1) := by
    unfold crkPhiFun
    rw [crkMkPartition_parts]
  have hdecΦ := crk_decode (phiList (Multiset.count 1 π.parts) (nonOneParts π))
    (crk_phi_sorted _ _ hl_sorted hlen) (crk_phi_ge_two _ _ (crk_nonOne_ge_two π))
    (phiPivot (Multiset.count 1 π.parts) (nonOneParts π)) _ hpartsΦ
  have hpartsΨ : (crkPsiFun k L hk (crkPhiFun k L hk π hπ)
      (crkPhiFun_mem k L hk π hπ)).parts
      = (((psiList (Multiset.count 1 (crkPhiFun k L hk π hπ).parts)
          (nonOneParts (crkPhiFun k L hk π hπ)) : Multiset ℕ))
        + Multiset.replicate
          (psiCount (Multiset.count 1 (crkPhiFun k L hk π hπ).parts)
            (nonOneParts (crkPhiFun k L hk π hπ))) 1) := by
    unfold crkPsiFun
    rw [crkMkPartition_parts]
  apply Nat.Partition.ext
  rw [hpartsΨ, hdecΦ.1, hdecΦ.2]
  have hN9 := crk_psi_phi _ _ hl_sorted hlen
  rw [hN9.1, hN9.2]
  exact (crk_parts_eq_nonOne_add π).symm

private theorem crk_fun_right_inv (k L : ℕ) (hk : 1 ≤ k) (ν : Nat.Partition L)
    (hν : partitionCrank ν ≤ -(((k + 1 : ℕ) : ℕ) : ℤ)) :
    crkPhiFun k L hk (crkPsiFun k L hk ν hν)
      (crkPsiFun_mem k L hk ν hν) = ν := by
  obtain ⟨-, hbig⟩ := crk_psi_index k L hk ν hν
  have hl_sorted := crk_nonOne_sorted ν
  have hpartsΨ : (crkPsiFun k L hk ν hν).parts
      = (((psiList (Multiset.count 1 ν.parts) (nonOneParts ν) : Multiset ℕ))
        + Multiset.replicate
          (psiCount (Multiset.count 1 ν.parts) (nonOneParts ν)) 1) := by
    unfold crkPsiFun
    rw [crkMkPartition_parts]
  have hdecΨ := crk_decode (psiList (Multiset.count 1 ν.parts) (nonOneParts ν))
    (crk_psi_sorted (Multiset.count 1 ν.parts) (nonOneParts ν) hl_sorted)
    (crk_psi_ge_two k _ _ hk hl_sorted (crk_nonOne_ge_two ν) hbig)
    (psiCount (Multiset.count 1 ν.parts) (nonOneParts ν)) _ hpartsΨ
  have hpartsΦ : (crkPhiFun k L hk (crkPsiFun k L hk ν hν)
      (crkPsiFun_mem k L hk ν hν)).parts
      = (((phiList (Multiset.count 1 (crkPsiFun k L hk ν hν).parts)
          (nonOneParts (crkPsiFun k L hk ν hν)) : Multiset ℕ))
        + Multiset.replicate
          (phiPivot (Multiset.count 1 (crkPsiFun k L hk ν hν).parts)
            (nonOneParts (crkPsiFun k L hk ν hν))) 1) := by
    unfold crkPhiFun
    rw [crkMkPartition_parts]
  apply Nat.Partition.ext
  rw [hpartsΦ, hdecΨ.1, hdecΨ.2]
  have hN9 := crk_phi_psi (Multiset.count 1 ν.parts) (nonOneParts ν) hl_sorted
  have hpiv2 : phiPivot (psiCount (Multiset.count 1 ν.parts) (nonOneParts ν))
      (psiList (Multiset.count 1 ν.parts) (nonOneParts ν))
      = Multiset.count 1 ν.parts := hN9.1
  rw [hN9.2, hpiv2]
  exact (crk_parts_eq_nonOne_add ν).symm

private noncomputable def crkEquivPhiPsi (k L : ℕ) (hk : 1 ≤ k) :
    { π : Nat.Partition L // highPartsCond k π } ≃
    { ν : Nat.Partition L // partitionCrank ν ≤ -(((k + 1 : ℕ) : ℕ) : ℤ) } where
  toFun s := ⟨crkPhiFun k L hk s.1 s.2, crkPhiFun_mem k L hk s.1 s.2⟩
  invFun t := ⟨crkPsiFun k L hk t.1 t.2, crkPsiFun_mem k L hk t.1 t.2⟩
  left_inv s := by
    apply Subtype.ext
    exact crk_fun_left_inv k L hk s.1 s.2
  right_inv t := by
    apply Subtype.ext
    exact crk_fun_right_inv k L hk t.1 t.2

private theorem crk_card_highParts_eq (k L : ℕ) (hk : 1 ≤ k) :
    Fintype.card { π : Nat.Partition L // highPartsCond k π } = crankLeCount (k + 1) L := by
  unfold crankLeCount
  exact Fintype.card_congr (crkEquivPhiPsi k L hk)

/-! ## Alternating sum recursion -/

private theorem crkE_zero (k : ℕ) : crkE k 0 = 0 := by
  unfold crkE
  simp

private theorem crkE_succ (k m : ℕ) (hk : 1 ≤ k) : crkE k (m + 1) = k + crkE (k + 1) m := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have ht := Nat.triangle_succ (m + 1)
  unfold crkE
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel] at ht ⊢
  rw [ht]
  have e1 : (m + 1) * j = m * j + j := by ring
  have e2 : m * (j + 1) = m * j + m := by ring
  omega

private theorem crkE_ge (k m : ℕ) (hk : 1 ≤ k) : m * k ≤ crkE k m := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have ht := Nat.triangle_succ m
  unfold crkE
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel] at ht ⊢
  have e : m * (j + 1) = m * j + m := by ring
  omega

private theorem crk_alt_lt (k M : ℕ) (hk : 1 ≤ k) (hM : M < k) :
    crankAltSum k M = (Fintype.card (Nat.Partition M) : ℤ) := by
  unfold crankAltSum
  rw [Finset.sum_eq_single 0]
  · simp only [crkE_zero, Nat.zero_le, ↓reduceIte, pow_zero, one_mul, Nat.sub_zero]
  · intro m _ hm0
    have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
    have hge := crkE_ge k m hk
    have hk2 : k ≤ m * k := by
      have h := Nat.mul_le_mul hm1 (le_refl k)
      rwa [Nat.one_mul] at h
    have hneg : ¬ crkE k m ≤ M := by omega
    simp [hneg]
  · intro hcon
    exact absurd (Finset.mem_range.mpr (by omega : (0 : ℕ) < M + 1)) hcon

private theorem crk_alt_add (k L : ℕ) (hk : 1 ≤ k) :
    crankAltSum k (L + k) =
    (Fintype.card (Nat.Partition (L + k)) : ℤ) - crankAltSum (k + 1) L := by
  have hterm : ∀ i : ℕ,
      (if crkE k (i + 1) ≤ L + k then (-1 : ℤ) ^ (i + 1) *
        (Fintype.card (Nat.Partition (L + k - crkE k (i + 1))) : ℤ) else 0)
      = -(if crkE (k + 1) i ≤ L then (-1 : ℤ) ^ i *
        (Fintype.card (Nat.Partition (L - crkE (k + 1) i)) : ℤ) else 0) := by
    intro i
    by_cases hg : crkE (k + 1) i ≤ L
    · have e1 := crkE_succ k i hk
      have g1 : k + crkE (k + 1) i ≤ L + k := by omega
      have hsub : (L + k) - (k + crkE (k + 1) i) = L - crkE (k + 1) i := by omega
      have hpow : (-1 : ℤ) ^ (i + 1) = -(-1 : ℤ) ^ i := by
        rw [pow_succ]
        ring
      simp only [g1, hg, ↓reduceIte, crkE_succ k i hk, hsub, hpow, neg_mul]
    · have e1 := crkE_succ k i hk
      have g1 : ¬ crkE k (i + 1) ≤ L + k := by omega
      simp only [g1, hg, ↓reduceIte, neg_zero]
  have hvanish : (∑ m ∈ Finset.range (L + k),
        (if crkE (k + 1) m ≤ L then (-1 : ℤ) ^ m *
          (Fintype.card (Nat.Partition (L - crkE (k + 1) m)) : ℤ) else 0))
      = (∑ m ∈ Finset.range (L + 1),
        (if crkE (k + 1) m ≤ L then (-1 : ℤ) ^ m *
          (Fintype.card (Nat.Partition (L - crkE (k + 1) m)) : ℤ) else 0)) := by
    have hsub : Finset.range (L + 1) ⊆ Finset.range (L + k) := by
      intro x hx
      rw [Finset.mem_range] at hx ⊢
      omega
    have hvsym : (∑ m ∈ Finset.range (L + 1),
          (if crkE (k + 1) m ≤ L then (-1 : ℤ) ^ m *
            (Fintype.card (Nat.Partition (L - crkE (k + 1) m)) : ℤ) else 0))
        = (∑ m ∈ Finset.range (L + k),
          (if crkE (k + 1) m ≤ L then (-1 : ℤ) ^ m *
            (Fintype.card (Nat.Partition (L - crkE (k + 1) m)) : ℤ) else 0)) :=
      Finset.sum_subset hsub (by
        intro x hxmem hxnot
        rw [Finset.mem_range] at hxmem hxnot
        have hge := crkE_ge (k + 1) x (by omega : 1 ≤ k + 1)
        have hx1 : x ≤ x * (k + 1) := by
          have h := Nat.mul_le_mul (le_refl x) (by omega : 1 ≤ k + 1)
          rwa [Nat.mul_one] at h
        have hneg : ¬ crkE (k + 1) x ≤ L := by omega
        simp [hneg])
    exact hvsym.symm
  have hmain : (∑ i ∈ Finset.range (L + k),
        (if crkE k (i + 1) ≤ L + k then (-1 : ℤ) ^ (i + 1) *
          (Fintype.card (Nat.Partition (L + k - crkE k (i + 1))) : ℤ) else 0))
      = -(∑ m ∈ Finset.range (L + 1),
        (if crkE (k + 1) m ≤ L then (-1 : ℤ) ^ m *
          (Fintype.card (Nat.Partition (L - crkE (k + 1) m)) : ℤ) else 0)) := by
    calc (∑ i ∈ Finset.range (L + k), (if crkE k (i + 1) ≤ L + k then (-1:ℤ)^(i+1) *
          (Fintype.card (Nat.Partition (L + k - crkE k (i+1))) : ℤ) else 0))
        = ∑ m ∈ Finset.range (L + k), (-(if crkE (k + 1) m ≤ L then (-1:ℤ)^m *
          (Fintype.card (Nat.Partition (L - crkE (k + 1) m)) : ℤ) else 0)) :=
          Finset.sum_congr rfl (fun i _ => hterm i)
      _ = -(∑ m ∈ Finset.range (L + k), (if crkE (k + 1) m ≤ L then (-1:ℤ)^m *
          (Fintype.card (Nat.Partition (L - crkE (k + 1) m)) : ℤ) else 0)) := by
          simp only [Finset.sum_neg_distrib]
      _ = -(∑ m ∈ Finset.range (L + 1), (if crkE (k + 1) m ≤ L then (-1:ℤ)^m *
          (Fintype.card (Nat.Partition (L - crkE (k + 1) m)) : ℤ) else 0)) := by
          rw [hvanish]
  have hsplit : (∑ m ∈ Finset.range (L + k + 1),
        (if crkE k m ≤ L + k then (-1 : ℤ) ^ m *
          (Fintype.card (Nat.Partition (L + k - crkE k m)) : ℤ) else 0))
      = (∑ i ∈ Finset.range (L + k),
        (if crkE k (i + 1) ≤ L + k then (-1 : ℤ) ^ (i + 1) *
          (Fintype.card (Nat.Partition (L + k - crkE k (i + 1))) : ℤ) else 0))
        + (if crkE k 0 ≤ L + k then (-1 : ℤ) ^ (0 : ℕ) *
          (Fintype.card (Nat.Partition (L + k - crkE k 0)) : ℤ) else 0) :=
    Finset.sum_range_succ' _ _
  unfold crankAltSum
  rw [hsplit]
  simp only [crkE_zero, Nat.zero_le, ↓reduceIte, pow_zero, one_mul, Nat.sub_zero]
  rw [hmain]
  ring

/-! ## Identification of the counting function -/

private theorem crk_leCount_eq (M k : ℕ) (hk : 1 ≤ k) :
    (crankLeCount k M : ℤ) = (Fintype.card (Nat.Partition M) : ℤ) - crankAltSum k M := by
  have hR : ∀ (k L : ℕ), 1 ≤ k → crankLeCount k (L + k) + crankLeCount (k + 1) L
      = Fintype.card (Nat.Partition L) := by
    intro k L hk
    rw [← crk_card_highParts_eq k L hk]
    exact crk_add_card_highParts k L hk
  revert k hk
  induction M using Nat.strong_induction_on
  rename_i M ih
  intro k hk
  by_cases hMk : M < k
  · rw [crk_count_eq_zero_of_lt hk hMk, Nat.cast_zero, crk_alt_lt k M hk hMk]
    exact (sub_self _).symm
  · have hMk' : k ≤ M := le_of_not_gt hMk
    obtain ⟨L, rfl⟩ := Nat.exists_eq_add_of_le hMk'
    rw [Nat.add_comm k L]
    have hR' : (crankLeCount k (L + k) : ℤ) + (crankLeCount (k + 1) L : ℤ)
        = (Fintype.card (Nat.Partition L) : ℤ) := by
      exact_mod_cast hR k L hk
    have hIH : (crankLeCount (k + 1) L : ℤ)
        = (Fintype.card (Nat.Partition L) : ℤ) - crankAltSum (k + 1) L :=
      ih L (by omega) (k + 1) (by omega)
    have hA := crk_alt_add k L hk
    omega

end CrankNonneg

@[expose] public section

/-! # Non-negative crank generating function
-/

/--
**Partitions with non-negative crank.** For a partition $\lambda$, let $\omega(\lambda)$ be the
number of parts equal to $1$. The crank of $\lambda$ is its largest part if $\omega(\lambda) = 0$
(the largest part of the empty partition being $0$), and otherwise the number of parts greater
than $\omega(\lambda)$, counted with multiplicity, minus $\omega(\lambda)$. Let $p(k)$ be the
number of partitions of $k$. Then for every natural number $N$, the number of partitions of $N$
with non-negative crank equals

$$\sum_{n \ge 0,\ n(n+1)/2 \le N} (-1)^n \, p\bigl(N - n(n+1)/2\bigr).$$

This is the coefficient-wise form of the generating function for partitions with non-negative
crank. The source notes this result is originally due to Uncu.

Proves `Wanted` entry `crank_nonneg_partition_count`.

Source: George E. Andrews and David Newman, "The Minimal Excludant in
Integer Partitions," Journal of Integer Sequences 23 (2020),
Article 20.2.3, Theorem (label Theorem1, equation 1.11), lines 161–165,
https://cs.uwaterloo.ca/journals/JIS/VOL23/Andrews/andrews5.tex
-/
public theorem crank_nonneg_partition_count
    (N : ℕ) :
    Fintype.card { P : Nat.Partition N //
      0 ≤ (if Multiset.count 1 P.parts = 0 then (P.parts.sup : ℤ)
        else (((P.parts.filter
          (fun i => Multiset.count 1 P.parts < i)).card : ℤ)
          - (Multiset.count 1 P.parts : ℤ)))}
    = ∑ n ∈ Finset.range (N + 1),
        (if (n + 1) * n / 2 ≤ N
          then (-1 : ℤ) ^ n * (Fintype.card (Nat.Partition (N - (n + 1) * n / 2)) : ℤ)
          else 0) := by
  have h1 := Fintype.card_subtype_compl (fun P : Nat.Partition N =>
    0 ≤ (if Multiset.count 1 P.parts = 0 then (P.parts.sup : ℤ)
      else (((P.parts.filter
        (fun i => Multiset.count 1 P.parts < i)).card : ℤ)
        - (Multiset.count 1 P.parts : ℤ))))
  have h2 : Fintype.card { P : Nat.Partition N //
      ¬ 0 ≤ (if Multiset.count 1 P.parts = 0 then (P.parts.sup : ℤ)
        else (((P.parts.filter
          (fun i => Multiset.count 1 P.parts < i)).card : ℤ)
          - (Multiset.count 1 P.parts : ℤ)))} = CrankNonneg.crankLeCount 1 N := by
    unfold CrankNonneg.crankLeCount
    apply Fintype.card_congr
    apply Equiv.subtypeEquivRight
    intro P
    unfold CrankNonneg.partitionCrank
    constructor <;> intro h <;> omega
  have hle := Fintype.card_subtype_le (fun P : Nat.Partition N =>
    0 ≤ (if Multiset.count 1 P.parts = 0 then (P.parts.sup : ℤ)
      else (((P.parts.filter
        (fun i => Multiset.count 1 P.parts < i)).card : ℤ)
        - (Multiset.count 1 P.parts : ℤ))))
  have hN : Fintype.card { P : Nat.Partition N //
      0 ≤ (if Multiset.count 1 P.parts = 0 then (P.parts.sup : ℤ)
        else (((P.parts.filter
          (fun i => Multiset.count 1 P.parts < i)).card : ℤ)
          - (Multiset.count 1 P.parts : ℤ)))} + CrankNonneg.crankLeCount 1 N
      = Fintype.card (Nat.Partition N) := by
    omega
  have hsplit : ((Fintype.card { P : Nat.Partition N //
      0 ≤ (if Multiset.count 1 P.parts = 0 then (P.parts.sup : ℤ)
        else (((P.parts.filter
          (fun i => Multiset.count 1 P.parts < i)).card : ℤ)
          - (Multiset.count 1 P.parts : ℤ)))} : ℕ) : ℤ)
      = (Fintype.card (Nat.Partition N) : ℤ) - (CrankNonneg.crankLeCount 1 N : ℤ) := by
    omega
  have h13 := CrankNonneg.crk_leCount_eq N 1 (by omega : 1 ≤ 1)
  have hSR : CrankNonneg.crankAltSum 1 N = ∑ n ∈ Finset.range (N + 1),
      (if (n + 1) * n / 2 ≤ N
        then (-1 : ℤ) ^ n * (Fintype.card (Nat.Partition (N - (n + 1) * n / 2)) : ℤ)
        else 0) := by
    unfold CrankNonneg.crankAltSum
    apply Finset.sum_congr rfl
    intro m _
    have he : CrankNonneg.crkE 1 m = (m + 1) * m / 2 := by
      unfold CrankNonneg.crkE
      simp
    rw [he]
  omega

end

end MetaMathlibExt
