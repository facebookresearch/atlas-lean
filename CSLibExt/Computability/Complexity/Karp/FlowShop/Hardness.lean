/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.FlowShop.Basic
import CSLibExt.Computability.Complexity.Karp.PartitionComplete
import CSLibExt.Computability.Complexity.PolynomialEncoding.PairSplit
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.IntervalCases
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# NP-hardness of three-machine flow-shop scheduling

We reduce PARTITION to flow-shop scheduling and implement the reduction on the binary encodings.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FlowShop

open BitstringEncoding
open Cslib.Complexity.PolynomialEncoding

-- The separator job occupies the entire deadline by itself. Its zero-time operation on
-- machine two splits that machine's available time into two windows of length b.
private def gadget (as : List ℕ) (b : ℕ) : FlowShopInstance :=
  ([b, 0, b] :: as.map (fun a => [0, a, 0]), 2 * b)

private theorem gadget_wellFormed (as : List ℕ) (b : ℕ) : WellFormed (gadget as b) := by
  simp [WellFormed, gadget]

-- Disjoint half-open intervals contained in [lo, hi) have total length at most hi - lo.
private theorem capacity {idx : Finset ℕ} {t a : ℕ → ℕ} {lo hi : ℕ}
    (hlo : ∀ j ∈ idx, lo ≤ t j) (hhi : ∀ j ∈ idx, t j + a j ≤ hi)
    (hsep : ∀ j ∈ idx, ∀ k ∈ idx, j < k →
      t j + a j ≤ t k ∨ t k + a k ≤ t j) :
    idx.sum a ≤ hi - lo := by
  let slots (j : ℕ) := Finset.Ico (t j) (t j + a j)
  have hd : (idx : Set ℕ).PairwiseDisjoint slots := by
    intro j hj k hk hne
    have hsep' : t j + a j ≤ t k ∨ t k + a k ≤ t j := by
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact hsep j hj k hk hlt
      · exact (hsep k hk j hj hgt).symm
    apply Finset.disjoint_left.mpr
    intro z hz hzk
    have hz' := Finset.mem_Ico.mp hz
    have hzk' := Finset.mem_Ico.mp hzk
    omega
  have hsub : idx.biUnion slots ⊆ Finset.Ico lo hi := by
    intro z hz
    obtain ⟨j, hj, hz⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨h₁, h₂⟩ := Finset.mem_Ico.mp hz
    exact Finset.mem_Ico.mpr ⟨(hlo j hj).trans h₁, h₂.trans_le (hhi j hj)⟩
  simpa [Finset.card_biUnion hd, slots] using Finset.card_le_card hsub

private theorem map_range_getD (as : List ℕ) :
    (List.range as.length).map (fun j => as.getD j 0) = as := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp only [List.length_cons, List.range_succ_eq_map, List.map_cons, List.getD_cons_zero,
      List.map_map, Function.comp_def, List.getD_cons_succ, ih]

private theorem sum_range_getD (as : List ℕ) :
    (Finset.range as.length).sum (fun j => as.getD j 0) = as.sum := by
  induction as with
  | nil => simp
  | cons a as ih =>
    simp only [List.length_cons, Finset.sum_range_succ', List.getD_cons_succ,
      List.getD_cons_zero, List.sum_cons, ih, Nat.add_comm]

private theorem gadget_backward {as : List ℕ} {b : ℕ} (hsum : as.sum = 2 * b)
    (h : FlowShopFeasible (gadget as b)) :
    ∃ s : List ℕ, s.Sublist as ∧ s.sum = b := by
  obtain ⟨start, _, _, hjob, hmachine⟩ := h
  let t (j : ℕ) := (start.getD (j + 1) []).getD 1 0
  let a (j : ℕ) := as.getD j 0
  let middle := (start.getD 0 []).getD 1 0
  have hd : (gadget as b).1.length = as.length + 1 := by simp [gadget]
  have hd₀ : (gadget as b).1.getD 0 [] = [b, 0, b] := rfl
  have hd' (j : ℕ) (hj : j < as.length) :
      (gadget as b).1.getD (j + 1) [] = [0, a j, 0] := by
    simp only [gadget, List.getD_cons_succ]
    rw [← List.getElem_eq_getD [] (h := by simpa using hj), List.getElem_map,
      List.getElem_eq_getD 0]
  have hb : middle = b := by
    obtain ⟨h₀, h₁, h₂⟩ := hjob 0 (by omega)
    dsimp [middle]
    simp [gadget] at h₀ h₁ h₂ ⊢
    omega
  have hsplit (j : ℕ) (hj : j < as.length) :
      t j + a j ≤ b ∨ b ≤ t j := by
    have hh := hmachine 1 (by decide) 0 (by omega) (j + 1) (by omega) (by omega)
    rw [hd₀, hd' j hj] at hh
    change middle + 0 ≤ t j ∨ t j + a j ≤ middle at hh
    rw [hb] at hh
    exact (by simpa using hh.symm)
  have hdeadline (j : ℕ) (hj : j < as.length) : t j + a j ≤ 2 * b := by
    obtain ⟨_, h₁, h₂⟩ := hjob (j + 1) (by omega)
    rw [hd' j hj] at h₁ h₂
    change t j + a j ≤ (start.getD (j + 1) []).getD 2 0 at h₁
    change (start.getD (j + 1) []).getD 2 0 + 0 ≤ 2 * b at h₂
    omega
  have hsep (j : ℕ) (hj : j < as.length) (k : ℕ) (hk : k < as.length) (hjk : j < k) :
      t j + a j ≤ t k ∨ t k + a k ≤ t j := by
    have hh := hmachine 1 (by decide) (j + 1) (by omega) (k + 1) (by omega) (by omega)
    rw [hd' j hj, hd' k hk] at hh
    exact hh
  let before (j : ℕ) := t j + a j ≤ b
  let all := Finset.range as.length
  let left := all.filter before
  let right := all.filter (fun j => ¬before j)
  have hl j (hj : j ∈ left) : j < as.length ∧ before j := by
    simpa [left, all] using hj
  have hr j (hj : j ∈ right) : j < as.length ∧ ¬before j := by
    simpa [right, all] using hj
  have hls : left.sum a ≤ b := by
    simpa using capacity (idx := left) (lo := 0) (hi := b)
      (fun _ _ => Nat.zero_le _) (fun j hj => (hl j hj).2)
      (fun j hj k hk => hsep j (hl j hj).1 k (hl k hk).1)
  have hrs : right.sum a ≤ b := by
    have hcap := capacity (idx := right) (lo := b) (hi := 2 * b)
      (fun j hj => (hsplit j (hr j hj).1).resolve_left (hr j hj).2)
      (fun j hj => hdeadline j (hr j hj).1)
      (fun j hj k hk => hsep j (hr j hj).1 k (hr k hk).1)
    omega
  have he : left.sum a + right.sum a = 2 * b := by
    rw [Finset.sum_filter_add_sum_filter_not all before a]
    exact (sum_range_getD as).trans hsum
  let picked := (List.range as.length).filter (fun j => decide (before j))
  have hset : picked.toFinset = left := by
    ext j
    simp [picked, left, all]
  have hnodup : picked.Nodup := List.nodup_range.filter _
  have hsub := (List.filter_sublist (p := fun j => decide (before j))
    (l := List.range as.length)).map a
  rw [map_range_getD as] at hsub
  refine ⟨picked.map a, hsub, ?_⟩
  rw [← List.sum_toFinset a hnodup, hset]
  omega

private theorem placeSublist {s as : List ℕ} (hs : s.Sublist as) {l r b d : ℕ}
    (hr : b ≤ r) (hl : l + s.sum ≤ b) (hrest : r + (as.sum - s.sum) ≤ d) :
    ∃ t : List ℕ, t.length = as.length ∧
      (∀ j < as.length, (l ≤ t.getD j 0 ∧ t.getD j 0 + as.getD j 0 ≤ b) ∨
        (r ≤ t.getD j 0 ∧ t.getD j 0 + as.getD j 0 ≤ d)) ∧
      ∀ j < as.length, ∀ k < as.length, j < k →
        t.getD j 0 + as.getD j 0 ≤ t.getD k 0 ∨
          t.getD k 0 + as.getD k 0 ≤ t.getD j 0 := by
  induction hs generalizing l r with
  | slnil => exact ⟨[], rfl, by simp, by simp⟩
  | @cons s as a hs ih =>
    have hsmall := hs.sum_le_sum (fun _ _ => Nat.zero_le _)
    simp only [List.sum_cons] at hrest
    obtain ⟨t, ht, hwin, hpair⟩ :=
      ih (l := l) (r := r + a) (by omega) hl (by omega)
    refine ⟨r :: t, by simp [ht], ?_, ?_⟩
    · rintro (_ | j) hj
      · exact Or.inr ⟨le_rfl, by simpa using (show r + a ≤ d by omega)⟩
      · simp only [List.getD_cons_succ]
        rcases hwin j (by simpa using hj) with h | h
        · exact Or.inl h
        · exact Or.inr ⟨by omega, h.2⟩
    · rintro (_ | j) hj (_ | k) hk hjk
      · omega
      · simp only [List.getD_cons_zero, List.getD_cons_succ]
        rcases hwin k (by simpa using hk) with h | h
        · exact Or.inr (h.2.trans hr)
        · exact Or.inl h.1
      · omega
      · simpa only [List.getD_cons_succ] using
          hpair j (by simpa using hj) k (by simpa using hk) (by omega)
  | @cons_cons s as a hs ih =>
    simp only [List.sum_cons] at hl hrest
    obtain ⟨t, ht, hwin, hpair⟩ :=
      ih (l := l + a) (r := r) hr (by omega) (by omega)
    refine ⟨l :: t, by simp [ht], ?_, ?_⟩
    · rintro (_ | j) hj
      · exact Or.inl ⟨le_rfl, by simpa using (show l + a ≤ b by omega)⟩
      · simp only [List.getD_cons_succ]
        rcases hwin j (by simpa using hj) with h | h
        · exact Or.inl ⟨by omega, h.2⟩
        · exact Or.inr h
    · rintro (_ | j) hj (_ | k) hk hjk
      · omega
      · simp only [List.getD_cons_zero, List.getD_cons_succ]
        rcases hwin k (by simpa using hk) with h | h
        · exact Or.inl h.1
        · exact Or.inl (by omega)
      · omega
      · simpa only [List.getD_cons_succ] using
          hpair j (by simpa using hj) k (by simpa using hk) (by omega)

private theorem gadget_forward {as : List ℕ} {b : ℕ} (hsum : as.sum = 2 * b)
    (h : ∃ s : List ℕ, s.Sublist as ∧ s.sum = b) :
    FlowShopFeasible (gadget as b) := by
  obtain ⟨s, hs, hsb⟩ := h
  obtain ⟨t, ht, hwin, hpair⟩ :=
    placeSublist hs (l := 0) (r := b) (b := b) (d := 2 * b)
      le_rfl (by omega) (by omega)
  let start := [0, b, b] :: t.map (fun n => [0, n, 2 * b])
  have hjobs : (gadget as b).1.length = as.length + 1 := by simp [gadget]
  have hrow (j : ℕ) (hj : j < as.length) :
      start.getD (j + 1) [] = [0, t.getD j 0, 2 * b] := by
    simp only [start, List.getD_cons_succ]
    rw [← List.getElem_eq_getD [] (h := by simpa [ht] using hj), List.getElem_map,
      List.getElem_eq_getD 0]
  have hjob (j : ℕ) (hj : j < as.length) :
      (gadget as b).1.getD (j + 1) [] = [0, as.getD j 0, 0] := by
    simp only [gadget, List.getD_cons_succ]
    rw [← List.getElem_eq_getD [] (h := by simpa using hj), List.getElem_map,
      List.getElem_eq_getD 0]
  refine ⟨start, by simp [start, gadget, ht], by simp [start], ?_, ?_⟩
  · rintro (_ | j) hj
    · change 0 + b ≤ b ∧ b + 0 ≤ b ∧ b + b ≤ 2 * b
      omega
    · have hj' : j < as.length := by omega
      rw [hrow j hj', hjob j hj']
      change 0 + 0 ≤ t.getD j 0 ∧ t.getD j 0 + as.getD j 0 ≤ 2 * b ∧
        2 * b + 0 ≤ 2 * b
      rcases hwin j hj' with h | h <;> omega
  · intro k hk
    rintro (_ | j) hj (_ | m) hm hjm
    · omega
    · have hm' : m < as.length := by omega
      rw [hrow m hm', hjob m hm']
      change [0, b, b].getD k 0 + [b, 0, b].getD k 0 ≤ [0, t.getD m 0, 2 * b].getD k 0 ∨
        [0, t.getD m 0, 2 * b].getD k 0 + [0, as.getD m 0, 0].getD k 0 ≤ [0, b, b].getD k 0
      interval_cases k <;> simp only [List.getD_cons_zero, List.getD_cons_succ] <;>
        rcases hwin m hm' with h | h <;> omega
    · omega
    · have hj' : j < as.length := by omega
      have hm' : m < as.length := by omega
      rw [hrow j hj', hjob j hj', hrow m hm', hjob m hm']
      interval_cases k
      · simp
      · simpa using hpair j hj' m hm' (by omega)
      · simp

private theorem gadget_feasible (as : List ℕ) :
    FlowShopFeasible (gadget (as.map (· * 2)) as.sum) ↔ Partition.PartitionFeasible as := by
  have hsum : (as.map (· * 2)).sum = 2 * as.sum := by
    simpa [Nat.mul_comm] using List.sum_map_mul_right as id 2
  rw [Partition.feasible_iff_doubled_sublist]
  exact ⟨gadget_backward hsum, gadget_forward hsum⟩

private def reducePartition (x : List Bool) : List Bool :=
  match bitDecode (α := List ℕ) x with
  | none => []
  | some as => bitEncode (gadget (as.map (· * 2)) as.sum)

private theorem reducePartition_correct (x : List Bool) :
    Partition.partitionDec x = flowShopDec (reducePartition x) := by
  cases hd : bitDecode (α := List ℕ) x with
  | none => simp [reducePartition, Partition.partitionDec, hd]; rfl
  | some as =>
    simp only [reducePartition, hd, Partition.partitionDec, flowShopDec, bitDecode_bitEncode]
    apply Bool.eq_iff_iff.mpr
    simp [gadget_wellFormed, gadget_feasible]

/-! ## Polynomial-time construction

The existing PARTITION-to-SUBSET-SUM machine produces a target and a list of doubled
weights. This component rewrites their frames into flow-shop jobs and a doubled deadline.
-/

namespace Reframe

open Cslib.Complexity.Karp Computability
open Turing Function TM2Program TM2Embedding

private def widen (bs : List Bool) : List Bool :=
  bs.flatMap fun b => [true, b]

private def widen₂ (bs : List Bool) : List Bool := widen (widen bs)

private def widen₃ (bs : List Bool) : List Bool := widen₂ (widen bs)

private theorem widen_append (xs ys : List Bool) :
    widen (xs ++ ys) = widen xs ++ widen ys := List.flatMap_append

private theorem widen₂_append (xs ys : List Bool) :
    widen₂ (xs ++ ys) = widen₂ xs ++ widen₂ ys := by
  simp only [widen₂, widen_append]

private theorem widen₃_append (xs ys : List Bool) :
    widen₃ (xs ++ ys) = widen₃ xs ++ widen₃ ys := by
  simp only [widen₃, widen_append, widen₂_append]

private theorem delimit_eq (xs : List Bool) :
    delimit xs = widen xs ++ [false] := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    change true :: b :: delimit xs = true :: b :: (widen xs ++ [false])
    rw [ih]

private inductive Phase | start | marker | payload
  deriving DecidableEq

private def nextPhase : Phase → Bool → Phase
  | .payload, _ => .marker
  | _, true => .payload
  | _, false => .start

private def rowPrefix : List Bool := widen₂ [false]
private def suffix : List Bool := widen₂ [false, false] ++ widen [false]

private def chunk : Phase → Bool → List Bool
  | .start, true => rowPrefix ++ widen₂ [true]
  | .start, false => rowPrefix ++ suffix
  | .marker, false => suffix
  | _, b => widen₂ [b]

private def items : Phase → List Bool → List Bool
  | _, [] => []
  | q, b :: bs => chunk q b ++ items (nextPhase q b) bs

private theorem items_marker (p rest : List Bool) :
    items .marker (delimit p ++ rest) =
      widen₂ (delimit p) ++ widen₂ [false] ++ widen [false] ++ items .start rest := by
  induction p with
  | nil => simp only [delimit, List.singleton_append, items, chunk, suffix, nextPhase]
           rfl
  | cons b p ih =>
    simp only [delimit, List.cons_append, items, chunk, nextPhase, ih,
      ← List.append_assoc]
    rfl

private theorem items_start (p rest : List Bool) :
    items .start (delimit p ++ rest) =
      widen (delimit (bitEncode ([0] : List ℕ) ++ delimit p ++ [false])) ++
        items .start rest := by
  cases p with
  | nil => rfl
  | cons b p =>
    have he : bitEncode ([0] : List ℕ) = [false] := rfl
    rw [he, delimit_eq ([false] ++ delimit (b :: p) ++ [false]),
      widen_append, ← widen₂, widen₂_append, widen₂_append]
    simp only [delimit, List.cons_append, items, chunk, nextPhase, items_marker,
      ← List.append_assoc, rowPrefix]
    rfl

private theorem items_encode (as : List ℕ) :
    items .start (as.flatMap fun a => delimit (encodeNat a)) =
      widen (bitEncode (as.map fun a => [0, a, 0])) := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp only [List.flatMap_cons, items_start, ih, List.map_cons]
    change widen (delimit (bitEncode ([0] : List ℕ) ++ delimit (encodeNat a) ++ [false])) ++
      widen (bitEncode (as.map fun a => [0, a, 0])) =
      widen (delimit (bitEncode ([0, a, 0] : List ℕ)) ++
        bitEncode (as.map fun a => [0, a, 0]))
    rw [widen_append]
    rfl

private def doubleBits : List Bool → List Bool
  | [] => []
  | b :: bs => false :: b :: bs

private theorem doubleBits_encodeNat (n : ℕ) : doubleBits (encodeNat n) = encodeNat (2 * n) := by
  by_cases hn : n = 0
  · subst n
    rfl
  · have hp : encodeNat n ≠ [] := by
      intro h
      have h' := decode_encodeNat n
      rw [h] at h'
      exact hn h'.symm
    have h : encodeNat (2 * n) = false :: encodeNat n := by
      rw [TM2Recursive.encodeNat_eq_cons (by omega : 2 * n ≠ 0)]
      simp
    rw [h]
    cases he : encodeNat n with
    | nil => exact (hp he).elim
    | cons b bs => rfl

private def assembled (p r : List Bool) : List Bool :=
  widen₃ p ++ widen₂ [false, false] ++ widen₃ p ++ widen₂ [false] ++
    widen [false] ++ items .start r ++ [false] ++ doubleBits p

private theorem assembled_encode (as : List ℕ) (b : ℕ) :
    assembled (encodeNat b) (as.flatMap fun a => delimit (encodeNat a)) =
      bitEncode (gadget as b) := by
  rw [assembled, doubleBits_encodeNat, items_encode]
  change _ = delimit
    (delimit (bitEncode ([b, 0, b] : List ℕ)) ++ bitEncode (as.map fun a => [0, a, 0])) ++
    encodeNat (2 * b)
  have hrow : bitEncode ([b, 0, b] : List ℕ) =
      delimit (encodeNat b) ++ ([false] ++ delimit (encodeNat b)) := by
    change delimit (encodeNat b) ++ ([false] ++ (delimit (encodeNat b) ++ [])) = _
    rw [List.append_nil]
  rw [hrow, delimit_eq (_ ++ bitEncode _), widen_append, delimit_eq (_ ++ (_ ++ _)),
    widen_append, ← widen₂, widen₂_append, widen₂_append, delimit_eq (encodeNat b)]
  simp only [widen₂_append, widen₃, List.append_assoc]
  rfl

private def convert (x : List Bool) : List Bool :=
  match undelimit x with
  | none => []
  | some (p, r) => if r.isEmpty && !p.isEmpty then [] else assembled p r

private theorem convert_after_reduce :
    (fun x => convert (Partition.reduceToSubsetSum x)) = reducePartition := by
  funext x
  cases hd : bitDecode (α := List ℕ) x with
  | none =>
    simp only [Partition.reduceToSubsetSum, reducePartition, hd]
    rfl
  | some as =>
    simp only [Partition.reduceToSubsetSum, reducePartition, hd, convert,
      encodeSS, undelimit_delimit]
    rw [ite_eq_right, assembled_encode]
    cases as <;> simp [show encodeNat 0 = [] from rfl, SSVerify.delimit_ne_nil]

private inductive Rev | deadline | items | second | first
  deriving DecidableEq

private inductive K | pair (k : PairSplit.K) | rev (k : Rev) | out
  deriving DecidableEq

private inductive Lab
  | pair (l : PairSplit.Lab) | guard | target | item (q : Phase) | move (k : Rev)
  | deadlineEnds | endSeparator | middleSeparator | done
  deriving DecidableEq

private def pairEmb : SEmb (fun _ : PairSplit.K => Bool) (fun _ : K => Bool) where
  e := K.pair
  inj _ _ := K.pair.inj
  ι _ := Equiv.refl _

private def pairLabel : PairSplit.Lab → Lab
  | .good => .guard
  | .bad => .done
  | l => .pair l

private def nextMove : Rev → Lab
  | .deadline => .deadlineEnds
  | .items => .endSeparator
  | .second => .middleSeparator
  | .first => .done

private def prog : Lab → TM2.Stmt (fun _ : K => Bool) Lab Bool
  | .pair l => mapS pairEmb pairLabel (PairSplit.prog l)
  | .guard =>
    .peek (.pair .input) (fun _ o => o.isNone) <| .branch id
      (.peek (.pair .left) (fun _ o => o.isSome) <| .branch id
        (.goto fun _ => .done) (.goto fun _ => .target))
      (.goto fun _ => .target)
  | .target =>
    .peek (.pair .left) (fun _ o => o.isNone) <| .branch id
      (.goto fun _ => .item .start)
      (.pop (.pair .left) (fun _ o => o.getD false) <| .branch id
        (.push (.rev .deadline) id <|
          pushList (.rev .first) (widen₃ [true]) <|
          emit (.rev .second) (widen₃ [true]) .target)
        (.push (.rev .deadline) id <|
          pushList (.rev .first) (widen₃ [false]) <|
          emit (.rev .second) (widen₃ [false]) .target))
  | .item q =>
    .peek (.pair .input) (fun _ o => o.isNone) <| .branch id
      (.goto fun _ => .move .deadline)
      (.pop (.pair .input) (fun _ o => o.getD false) <| .branch id
        (emit (.rev .items) (chunk q true) (.item (nextPhase q true)))
        (emit (.rev .items) (chunk q false) (.item (nextPhase q false))))
  | .move k => moveB (.rev k) .out some id (.move k) (nextMove k)
  | .deadlineEnds =>
    .peek .out (fun _ o => o.isNone) <| .branch id
      (emitR .out [false] (.move .items)) (emitR .out [false, false] (.move .items))
  | .endSeparator => emitR .out (widen₂ [false] ++ widen [false]) (.move .second)
  | .middleSeparator => emitR .out (widen₂ [false, false]) (.move .first)
  | .done => .halt

private theorem embeds_pair : Embeds pairEmb pairLabel PairSplit.prog prog := by
  intro l
  cases l <;> simp [pairLabel, prog, PairSplit.prog]

private def st (p r d i a b o : List Bool) : K → List Bool
  | .pair .input => r
  | .pair .left => p
  | .pair .scratch => []
  | .rev .deadline => d
  | .rev .items => i
  | .rev .first => a
  | .rev .second => b
  | .out => o

@[simp] private theorem st_update_left (p r d i a b o x : List Bool) :
    update (st p r d i a b o) (.pair .left) x = st x r d i a b o := by
  funext k
  rcases k with k | k | _
  all_goals first | rfl | cases k <;> rfl

@[simp] private theorem st_update_input (p r d i a b o x : List Bool) :
    update (st p r d i a b o) (.pair .input) x = st p x d i a b o := by
  funext k
  rcases k with k | k | _
  all_goals first | rfl | cases k <;> rfl

@[simp] private theorem st_update_rev (k : Rev) (p r d i a b o x : List Bool) :
    update (st p r d i a b o) (.rev k) x =
      match k with
      | .deadline => st p r x i a b o
      | .items => st p r d x a b o
      | .first => st p r d i x b o
      | .second => st p r d i a x o := by
  funext j
  cases k <;> rcases j with j | j | _
  all_goals first | rfl | cases j <;> rfl

@[simp] private theorem st_update_out (p r d i a b o x : List Bool) :
    update (st p r d i a b o) .out x = st p r d i a b x := by
  funext k
  rcases k with k | k | _
  all_goals first | rfl | cases k <;> rfl

private theorem target_run (p : List Bool) :
    ∀ (r d a b : List Bool) (v : Bool),
      Run prog (p.length + 1) ⟨some .target, v, st p r d [] a b []⟩
        ⟨some (.item .start), true,
          st [] r (p.reverse ++ d) [] ((widen₃ p).reverse ++ a)
            ((widen₃ p).reverse ++ b) []⟩ := by
  induction p with
  | nil =>
    intro r d a b v
    exact Run.single (by simp [prog, TM2.stepAux, st]; rfl)
  | cons c p ih =>
    intro r d a b v
    have h := ih r (c :: d) ((widen₃ [c]).reverse ++ a) ((widen₃ [c]).reverse ++ b) c
    rw [show c :: p = [c] ++ p by rfl, widen₃_append, List.reverse_append,
      List.reverse_append, List.reverse_cons]
    simp only [← List.append_assoc] at h
    refine Run.head (d := ⟨some .target, c,
      st p r (c :: d) [] ((widen₃ [c]).reverse ++ a) ((widen₃ [c]).reverse ++ b) []⟩) ?_ ?_
    · cases c <;> simp [TM2.step, prog, TM2.stepAux, emit,
        stepAux_pushList, st, widen₃, widen₂, widen]
    · simpa only [List.reverse_nil, List.nil_append, List.append_assoc, List.singleton_append,
        List.length_cons]
        using h

private theorem item_run (r : List Bool) :
    ∀ (q : Phase) (d i a b : List Bool) (v : Bool),
      Run prog (r.length + 1) ⟨some (.item q), v, st [] r d i a b []⟩
        ⟨some (.move .deadline), true, st [] [] d ((items q r).reverse ++ i) a b []⟩ := by
  induction r with
  | nil =>
    intro q d i a b v
    exact Run.single (by simp [prog, TM2.stepAux, st, items])
  | cons c r ih =>
    intro q d i a b v
    have h := ih (nextPhase q c) d ((chunk q c).reverse ++ i) a b c
    simp only [items, List.reverse_append, List.append_assoc]
    refine Run.head ?_ h
    cases c <;> simp [TM2.step, prog, TM2.stepAux, emit, stepAux_pushList, st]

private theorem move_run (k : Rev) (d i a b o : List Bool) (v : Bool) :
    let S := st [] [] d i a b o
    let xs := S (.rev k)
    ∃ v', Run prog (xs.length + 1) ⟨some (.move k), v, S⟩
      ⟨some (nextMove k), v', update (update S (.rev k) []) .out (xs.reverse ++ o)⟩ := by
  intro S xs
  obtain ⟨v', S', hr, he, ho, hf⟩ := moveB_run (M := prog)
    (self := .move k) (next := nextMove k) (a := .rev k) (b := .out)
    (d := some) (g := id) rfl (by simp) xs xs [] v S (by simp [xs])
    (by simp [IsBitBlock]) (by simp [EndsBitBlock])
  refine ⟨v', ?_⟩
  have hs : S' = update (update S (.rev k) []) .out (xs.reverse ++ o) := by
    funext j
    by_cases hj : j = .out
    · subst j
      simpa [S, st] using ho
    by_cases hk : j = .rev k
    · subst j
      simpa [hj] using he
    · simpa [hj, hk] using hf j hk hj
  rwa [hs] at hr

private theorem widen_length (x : List Bool) : (widen x).length = 2 * x.length := by
  induction x with
  | nil => rfl
  | cons b x ih =>
    change (true :: b :: widen x).length = _
    simp only [List.length_cons, ih, Nat.mul_succ]

private theorem items_length (q : Phase) (r : List Bool) :
    (items q r).length ≤ 14 * r.length := by
  induction r generalizing q with
  | nil => exact le_rfl
  | cons b r ih =>
    have hb : (chunk q b).length ≤ 14 := by cases q <;> cases b <;> decide
    simp only [items, List.length_append, List.length_cons, Nat.mul_succ]
    exact Nat.add_le_add_right hb _ |>.trans (by have := ih (nextPhase q b); omega)

private theorem assemble_run (p r : List Bool) (v : Bool) :
    ∃ v', RunLe prog (20 * (p.length + r.length + 1))
      ⟨some .target, v, st p r [] [] [] [] []⟩
      ⟨some .done, v', st [] [] [] [] [] [] (assembled p r)⟩ := by
  let a := (widen₃ p).reverse
  let i := (items .start r).reverse
  have ht := target_run p r [] [] [] v
  simp only [List.append_nil] at ht
  have hi := item_run r .start p.reverse [] a a true
  simp only [List.append_nil] at hi
  obtain ⟨v₁, h₁⟩ := move_run .deadline p.reverse i a a [] true
  have hm₁ : Run prog (p.length + 1) ⟨some (.move .deadline), true,
      st [] [] p.reverse i a a []⟩ ⟨some .deadlineEnds, v₁, st [] [] [] i a a p⟩ := by
    simpa [st, nextMove] using h₁
  have hₑ : Run prog 1 ⟨some .deadlineEnds, v₁, st [] [] [] i a a p⟩
      ⟨some (.move .items), p.isEmpty, st [] [] [] i a a (false :: doubleBits p)⟩ := by
    apply Run.single
    cases p <;> simp [prog, TM2.stepAux, st, emitR, emit, stepAux_pushList, doubleBits]
  obtain ⟨v₂, h₂⟩ := move_run .items [] i a a (false :: doubleBits p) p.isEmpty
  let o₂ := items .start r ++ false :: doubleBits p
  have hm₂ : Run prog (i.length + 1)
      ⟨some (.move .items), p.isEmpty, st [] [] [] i a a (false :: doubleBits p)⟩
      ⟨some .endSeparator, v₂, st [] [] [] [] a a o₂⟩ := by
    simpa [i, o₂, nextMove, st] using h₂
  let o₃ := (widen₂ [false] ++ widen [false]) ++ o₂
  have h₃ : Run prog 1 ⟨some .endSeparator, v₂, st [] [] [] [] a a o₂⟩
      ⟨some (.move .second), v₂, st [] [] [] [] a a o₃⟩ := by
    simpa [o₃, st] using emitR_run (M := prog) (self := .endSeparator) (next := .move .second)
      (k := K.out) (ys := widen₂ [false] ++ widen [false]) rfl v₂ (st [] [] [] [] a a o₂)
  obtain ⟨v₄, h₄⟩ := move_run .second [] [] a a o₃ v₂
  let o₄ := widen₃ p ++ o₃
  have hm₄ : Run prog (a.length + 1) ⟨some (.move .second), v₂, st [] [] [] [] a a o₃⟩
      ⟨some .middleSeparator, v₄, st [] [] [] [] a [] o₄⟩ := by
    simpa [o₄, a, nextMove, st] using h₄
  let o₅ := widen₂ [false, false] ++ o₄
  have h₅ : Run prog 1 ⟨some .middleSeparator, v₄, st [] [] [] [] a [] o₄⟩
      ⟨some (.move .first), v₄, st [] [] [] [] a [] o₅⟩ := by
    simpa [o₅, st] using emitR_run (M := prog) (self := .middleSeparator) (next := .move .first)
      (k := K.out) (ys := widen₂ [false, false]) rfl v₄ (st [] [] [] [] a [] o₄)
  obtain ⟨v₆, h₆⟩ := move_run .first [] [] a [] o₅ v₄
  have hm₆ : Run prog (a.length + 1) ⟨some (.move .first), v₄, st [] [] [] [] a [] o₅⟩
      ⟨some .done, v₆, st [] [] [] [] [] [] (assembled p r)⟩ := by
    simpa [o₅, o₄, o₃, o₂, a, nextMove, st, assembled, List.append_assoc] using h₆
  refine ⟨v₆, (((((((ht.trans hi).trans hm₁).trans hₑ).trans hm₂).trans h₃).trans hm₄).trans
    h₅ |>.trans hm₆).le ?_⟩
  have hAlen : a.length = 8 * p.length := by
    simp [a, widen₃, widen₂, widen_length]
    omega
  have hIlen : i.length ≤ 14 * r.length := by simpa [i] using items_length .start r
  omega
private theorem run (x : List Bool) :
    ∃ v S, RunLe prog (22 * (x.length + 1))
      ⟨some (.pair .read), false, update (fun _ => []) (.pair .input) x⟩
      ⟨some .done, v, S⟩ ∧ S .out = convert x := by
  let init : K → List Bool := update (fun _ => []) (.pair .input) x
  obtain ⟨v, S, hrun, hframe, hagree⟩ := PairSplit.run_embedded pairEmb pairLabel
    embeds_pair x false init (by
      intro k
      cases k <;> simp [init, pairEmb, PairSplit.st])
  have hf (k : K) (hk : ∀ j, pairEmb.e j ≠ k) : S k = [] := by
    rw [hframe k hk]
    exact update_of_ne (f := fun _ : K => []) (v := x) (hk _).symm
  cases h : undelimit x with
  | none =>
    simp only [h, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, pairLabel] at hrun
    exact ⟨v, S, hrun.mono (by omega), by simp [convert, h, hf .out (fun _ => by simp [pairEmb])]⟩
  | some pr =>
    obtain ⟨p, r⟩ := pr
    simp only [h, Option.isSome_some, ↓reduceIte, pairLabel] at hrun
    have hl : p.length + r.length ≤ x.length := by
      have he := congrArg List.length
        ((Cslib.CookLevin.undelimit_eq_some_iff _ _ _).mp h)
      simp only [List.length_append, length_delimit] at he
      omega
    have hs : S = st p r [] [] [] [] [] := by
      funext k
      cases k with
      | pair k =>
        have ha := hagree p r h k
        cases k <;> simpa [pairEmb, st, PairSplit.st] using ha
      | rev k => cases k <;> exact hf _ (fun _ => by simp [pairEmb])
      | out => exact hf _ (fun _ => by simp [pairEmb])
    rw [hs] at hrun
    cases hreject : r.isEmpty && !p.isEmpty
    · have hg : ∃ v', Run prog 1
          ⟨some .guard, v, st p r [] [] [] [] []⟩
          ⟨some .target, v', st p r [] [] [] [] []⟩ := by
        cases r <;> cases p <;>
          simp at hreject <;> exact ⟨false, Run.single (by rfl)⟩
      obtain ⟨v', hg⟩ := hg
      obtain ⟨v'', hr⟩ := assemble_run p r v'
      refine ⟨v'', st [] [] [] [] [] [] (assembled p r),
        ((hrun.trans (hg.le le_rfl)).trans hr).mono (by omega), ?_⟩
      simp [st, convert, h, hreject]
    · have hg : Run prog 1 ⟨some .guard, v, st p r [] [] [] [] []⟩
          ⟨some .done, true, st p r [] [] [] [] []⟩ := by
        cases r <;> cases p <;> simp at hreject
        exact Run.single (by rfl)
      exact ⟨true, st p r [] [] [] [] [], (hrun.trans (hg.le le_rfl)).mono (by omega),
        by simp [st, convert, h, hreject]⟩

private def keys : List K :=
  [.pair .input, .pair .left, .pair .scratch,
    .rev .deadline, .rev .items, .rev .first, .rev .second, .out]

private theorem mem_keys (k : K) : k ∈ keys := by
  cases k with
  | pair k => cases k <;> decide
  | rev k => cases k <;> decide
  | out => decide

private instance fintypeK : Fintype K := Fintype.ofList keys mem_keys

private instance fintypeLab : Fintype Lab := Fintype.ofList
  [.pair .read, .pair .copy, .pair .good, .pair .bad, .guard, .target,
    .item .start, .item .marker, .item .payload, .move .deadline, .move .items,
    .move .first, .move .second, .deadlineEnds, .endSeparator, .middleSeparator, .done] (by
    intro l
    cases l with
    | pair l => cases l <;> decide
    | item q => cases q <;> decide
    | move k => cases k <;> decide
    | _ => decide)

private abbrev comp : Cslib.Complexity.Host.Comp where
  K := K
  Γ := fun _ => Bool
  L := Lab
  prog := prog
  ks := keys
  ks_nodup := by decide
  mem_ks := mem_keys

private theorem isPolyTime_convert : ComplexityTheory.IsPolyTime convert :=
  Cslib.Complexity.Host.isPolyTime_reduction
    (c := comp) (cX := .pair .input) (cO := .out) (gX := id)
    (start := .pair .read) (done := .done) (Equiv.refl Bool)
    convert (Polynomial.C 22 * (Polynomial.X + 1)) rfl fun x => by simpa using run x

private theorem isPolyTime_reducePartition : ComplexityTheory.IsPolyTime reducePartition := by
  rw [← convert_after_reduce]
  exact Partition.MembershipMachine.isPolyTime_reduceToSubsetSum.comp isPolyTime_convert

end Reframe

/-- **NP-hardness of three-machine flow-shop scheduling.** Every language in NP reduces in
polynomial time to the encoded three-machine flow shop.

Source: Reduction from `Partition.partition_npComplete` using a separator job that splits
the middle machine's time into two equal intervals. -/
theorem flowShop_hard :
    ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
      L ∈ MetaMathlibExt.ComplexityTheory.NP → Cslib.CookLevin.PolyManyOneRed L flowShopDec :=
  Cslib.Complexity.NPHard.of_polyManyOneRed Partition.partition_npComplete.2
    ⟨reducePartition, Reframe.isPolyTime_reducePartition, reducePartition_correct⟩

end MetaMathlibExt.Complexity.NPComplete.FlowShop
