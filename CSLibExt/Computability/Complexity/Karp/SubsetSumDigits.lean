/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.SubsetSum
public import CSLibExt.Computability.Complexity.SatVerifierSpec
public import MathlibExt.Computability.TuringMachine.Program
public import MathlibExt.Computability.TuringMachine.Recursive.OfTM2
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Karp reductions, VERTEX-COVER → SUBSET-SUM: the numbers as bit lists

Facts about `Cslib.Complexity.Karp.reduceSS` that the machine `EmitSS.prog`
(`Karp.SubsetSumEmit`) needs, stated on explicit bit lists.

* `bitsVal` (`TM2Recursive`) reads a bit list as a number, least significant bit first;
  `encodeNat_bitsVal`: a list not ending in `false` is the binary code of its value, and
  `encodeNat_bitsVal_rev` drops trailing zeros otherwise.
* `vtxNum_eq_bitsVal`, `ssTarget_eq_bitsVal`, `edgeEnc_eq`: the vertex numbers, the target and the
  edge numbers as bit lists of base-4 digits (digit `q` = bits `2q`, `2q + 1`); `delimit_vtx`
  gives the delimited vertex number as four output bits `blk t` per digit.
* `walkM`: the pairs of marks met by walking the vertex marks as a zipper (rows from the top of
  `L`, columns on `R`). `walkM_mkL`: for the marks of `0, …, n - 1` it meets `pairs n` from the
  last pair to the first, so `walk_touches` recovers `touches`; `length_pairs_eq_tri`: `tri n`
  pairs.
-/

@[expose] public section

namespace Cslib.Complexity.Karp.EmitSS

open Function MetaMathlibExt.TM2Program Cslib.CookLevin Cslib.Complexity.SatVerifier
  Computability MetaMathlibExt.BitstringEncoding

/-! ### Bit lists and the numbers of the reduction -/

open MetaMathlibExt.TM2Recursive (bitsVal bitsVal_encodeNat)

/-- `bitsVal` (least significant bit first) of the empty list. -/
@[simp] theorem bitsVal_nil : bitsVal [] = 0 := rfl

/-- `bitsVal` peels the least significant bit. -/
@[simp] theorem bitsVal_cons (b : Bool) (l : List Bool) :
    bitsVal (b :: l) = b.toNat + 2 * bitsVal l := by
  cases b <;> simp [bitsVal] <;> omega

theorem bitsVal_append (l l' : List Bool) :
    bitsVal (l ++ l') = bitsVal l + 2 ^ l.length * bitsVal l' := by
  induction l with
  | nil => simp
  | cons b l ih =>
      simp only [List.cons_append, bitsVal_cons, ih, List.length_cons, pow_succ]; ring

theorem bitsVal_eq_zero {l : List Bool} (h : ∀ b ∈ l, b = false) : bitsVal l = 0 := by
  induction l with
  | nil => rfl
  | cons b l ih =>
      simp only [List.mem_cons, forall_eq_or_imp] at h
      simp [h.1, ih h.2]

/-- A bit list not ending in `false` is the binary code of its value. -/
theorem encodeNat_bitsVal : ∀ l : List Bool, l.getLast? ≠ some false → encodeNat (bitsVal l) = l
  | [], _ => rfl
  | b :: l, h => by
      have hl : l.getLast? ≠ some false := by
        cases l with
        | nil => simp
        | cons c l => simpa [List.getLast?_cons_cons] using h
      have ih := encodeNat_bitsVal l hl
      by_cases h0 : bitsVal (b :: l) = 0
      · simp only [bitsVal_cons, bitsVal_nil, Nat.add_eq_zero_iff, Bool.toNat_eq_zero, mul_eq_zero,
          OfNat.ofNat_ne_zero, false_or] at h0
        rw [h0.2] at ih
        obtain ⟨rfl, -⟩ := h0
        rw [← ih] at h
        exact absurd rfl h
      · rw [MetaMathlibExt.TM2Recursive.encodeNat_eq_cons h0]
        have h2 : bitsVal (b :: l) / 2 = bitsVal l := by cases b <;> simp; omega
        rw [h2, ih]
        cases b <;> simp

theorem encodeNat_getLast (k : ℕ) : (encodeNat k).getLast? ≠ some false := by
  rcases (encodeNat_decodeNat_eq_iff (encodeNat k)).1 (by rw [decode_encodeNat]) with h | h <;>
    simp [h]

theorem encodeNat_length_le (k : ℕ) : (encodeNat k).length ≤ k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp [MetaMathlibExt.TM2Recursive.encodeNat_zero]
      · rw [MetaMathlibExt.TM2Recursive.encodeNat_eq_cons (by omega), List.length_cons]
        have := ih (k / 2) (by omega)
        omega

/-- Values of bit lists made of two-bit digits. -/
theorem bitsVal_flatMap2 (f : Bool → List Bool) (hf : ∀ b, (f b).length = 2) :
    ∀ bs : List Bool, bitsVal (bs.flatMap f) =
      ((List.range bs.length).map fun q => 4 ^ q * bitsVal (f (bs.getD q false))).sum
  | [] => rfl
  | b :: bs => by
      rw [List.flatMap_cons, bitsVal_append, hf, bitsVal_flatMap2 f hf bs, List.length_cons,
        List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
      have : ∀ q, ((fun q => 4 ^ q * bitsVal (f ((b :: bs).getD q false))) ∘ Nat.succ) q =
          4 * (4 ^ q * bitsVal (f (bs.getD q false))) := fun q => by simp [pow_succ]; ring
      rw [List.map_congr_left (fun q _ => this q), List.sum_map_mul_left]
      simp

theorem sum_filter_map (qs : List ℕ) (p : ℕ → Bool) (g : ℕ → ℕ) :
    ((qs.filter p).map g).sum = (qs.map fun q => if p q then g q else 0).sum := by
  induction qs with
  | nil => rfl
  | cons q qs ih => by_cases h : p q <;> simp [h, ih]

theorem getD_map_range {m q : ℕ} (t : ℕ → Bool) (hq : q < m) :
    ((List.range m).map t).getD q false = t q := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hq]; rfl

theorem length_flatMap2 (f : Bool → List Bool) (hf : ∀ b, (f b).length = 2) (bs : List Bool) :
    (bs.flatMap f).length = 2 * bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih => rw [List.flatMap_cons, List.length_append, hf, ih, List.length_cons]; ring

theorem vtxNum_eq_bitsVal (n : ℕ) (bits : List Bool) (v : ℕ) :
    vtxNum n bits v = bitsVal (((List.range (pairs n).length).map (touches n bits v)).flatMap
      (fun t => [t, false]) ++ [true]) := by
  rw [bitsVal_append, bitsVal_flatMap2 _ (fun _ => rfl), vtxNum, sum_filter_map,
    length_flatMap2 _ (fun _ => rfl), List.length_map, List.length_range, add_comm]
  congr 1
  · refine congrArg List.sum (List.map_congr_left fun q hq => ?_)
    rw [getD_map_range _ (List.mem_range.1 hq)]
    cases touches n bits v q <;> simp [pairDigit]
  · simp [pow_mul]

theorem ssTarget_eq_bitsVal (k n : ℕ) (bits : List Bool) (hb : bits.length = (pairs n).length) :
    ssTarget k n bits = bitsVal (bits.flatMap (fun b => [false, b]) ++ encodeNat k) := by
  rw [bitsVal_append, bitsVal_flatMap2 _ (fun _ => rfl), ssTarget, sum_filter_map,
    bitsVal_encodeNat,
    length_flatMap2 _ (fun _ => rfl), hb, add_comm]
  congr 1
  · refine congrArg List.sum (List.map_congr_left fun q _ => ?_)
    cases bits.getD q false <;> simp [pairDigit]; ring
  · simp [pow_mul, mul_comm]

/-- The binary code of the target: its digits with leading zeros dropped. -/
theorem encodeNat_bitsVal_rev (l : List Bool) :
    encodeNat (bitsVal l) = (l.reverse.dropWhile (!·)).reverse := by
  have hsplit := (List.takeWhile_append_dropWhile (p := (!·)) (l := l.reverse))
  have hl : l = (l.reverse.dropWhile (!·)).reverse ++ (l.reverse.takeWhile (!·)).reverse := by
    rw [← List.reverse_append, hsplit, List.reverse_reverse]
  conv_lhs => rw [hl]
  rw [bitsVal_append, bitsVal_eq_zero (l := (l.reverse.takeWhile (!·)).reverse) (fun b hb => by
    simpa using List.all_eq_true.1 List.all_takeWhile b (List.mem_reverse.1 hb)), mul_zero,
    add_zero]
  apply encodeNat_bitsVal
  rw [List.getLast?_reverse]
  have := List.head?_dropWhile_not (!·) l.reverse
  revert this
  cases (l.reverse.dropWhile (!·)).head? <;> simp

private theorem delimit_eq (l : List Bool) :
    delimit l = l.flatMap (fun b => [true, b]) ++ [false] := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [delimit, ih]

/-- A delimited block ending in `true`: the closing bits of the target's code. -/
theorem delimit_append_true (u : List Bool) :
    delimit (u ++ [true]) = u.flatMap (fun b => [true, b]) ++ [true, true, false] := by
  simp [delimit_eq, List.flatMap_append]

/-- The four output bits of one pair digit of a vertex number. -/
def blk (t : Bool) : List Bool := [true, t, true, false]

theorem delimit_vtx (n : ℕ) (bits : List Bool) (v : ℕ) :
    delimit (encodeNat (vtxNum n bits v)) =
      ((List.range (pairs n).length).map (touches n bits v)).flatMap blk ++
        [true, true, false] := by
  rw [vtxNum_eq_bitsVal, encodeNat_bitsVal _ (by simp)]
  simp [delimit_eq, List.flatMap_assoc]
  rfl

/-- The output of the edge number of pair `q` with bit `b`. -/
def edgeEnc (q : ℕ) (b : Bool) : List Bool :=
  if b then rep [true, false, true, false] q ++ [true, true, false] else [false]

theorem flatMap_replicate_false (q : ℕ) :
    (List.replicate (2 * q) false).flatMap (fun b => [true, b]) =
      rep [true, false, true, false] q := by
  induction q with
  | zero => rfl
  | succ q ih =>
      rw [rep_succ, ← ih, show 2 * (q + 1) = 2 + 2 * q by ring, List.replicate_add,
        List.flatMap_append]
      rfl

theorem edgeEnc_eq (bits : List Bool) (q : ℕ) :
    edgeEnc q (bits.getD q false) = delimit (encodeNat (edgeNum bits q)) := by
  unfold edgeEnc edgeNum pairDigit
  cases bits.getD q false
  · rfl
  · have h4 : bitsVal (List.replicate (2 * q) false ++ [true]) = 4 ^ q := by
      rw [bitsVal_append, bitsVal_eq_zero (fun b hb => (List.mem_replicate.1 hb).2)]
      simp [pow_mul]
    simp only [↓reduceIte]
    rw [← h4, encodeNat_bitsVal _ (by simp), delimit_eq, List.flatMap_append,
      flatMap_replicate_false]
    simp

/-- The edge numbers' output, for the pair bits listed from the last pair down. -/
def edgeOut : List Bool → List Bool
  | [] => []
  | b :: ds => edgeOut ds ++ edgeEnc ds.length b

theorem edgeOut_reverse (bits : List Bool) :
    edgeOut bits.reverse =
      (List.range bits.length).flatMap fun q => edgeEnc q (bits.getD q false) := by
  induction bits using List.reverseRecOn with
  | nil => rfl
  | append_singleton l b ih =>
      rw [List.reverse_append, List.reverse_singleton, List.singleton_append, edgeOut, ih,
        List.length_reverse, List.length_append, List.length_singleton, List.range_succ,
        List.flatMap_append, List.flatMap_singleton]
      congr 1
      · exact List.flatMap_congr fun q hq => by
          rw [List.getD_append _ _ _ _ (List.mem_range.1 hq)]
      · simp

/-! ### The pair walk -/

/-- The mark pairs a walk over the vertex marks meets: for the row vertex `a` on top of `L`, one
pair with every mark of `R`; then `a` moves onto `R`. -/
def walkM : List Bool → List Bool → List (Bool × Bool)
  | [], _ => []
  | a :: L, R => R.map (a, ·) ++ walkM L (a :: R)

/-- Triangular numbers: `tri n = 0 + 1 + ⋯ + (n - 1)`. -/
def tri : ℕ → ℕ
  | 0 => 0
  | i + 1 => tri i + i

theorem walkM_length : ∀ (L R : List Bool),
    (walkM L R).length = L.length * R.length + tri L.length
  | [], _ => by simp [walkM, tri]
  | a :: L, R => by
      rw [walkM, List.length_append, List.length_map, walkM_length L (a :: R)]
      simp only [List.length_cons, tri]
      ring

theorem filter_range_lt (i n : ℕ) :
    (List.range n).filter (fun j => decide (i < j)) = List.range' (i + 1) (n - (i + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.filter_append, ih]
      by_cases h : i < n
      · rw [show n + 1 - (i + 1) = n - (i + 1) + 1 by omega, List.range'_concat]
        simp [h, show i + 1 + (n - (i + 1)) = n by omega]
      · simp [h, show n + 1 - (i + 1) = 0 by omega, show n - (i + 1) = 0 by omega]

/-- The walk over the marks of vertices `0, …, n - 1` meets the pairs of `pairs n` from the last
to the first. -/
theorem walkM_pairs (f : ℕ → Bool) (n : ℕ) : ∀ i ≤ n,
    walkM ((List.range i).map f).reverse ((List.range' i (n - i)).map f) =
      ((List.range i).flatMap fun a =>
        ((List.range n).reverse.filter (a < ·)).map (a, ·)).reverse.map fun p => (f p.1, f p.2)
  | 0, _ => by simp [walkM]
  | i + 1, hi => by
      have ih := walkM_pairs f n i (by omega)
      rw [show n - i = n - (i + 1) + 1 by omega, List.range'_succ, List.map_cons] at ih
      rw [List.range_succ, List.map_append, List.reverse_append, List.map_singleton,
        List.reverse_singleton, List.singleton_append, walkM, ih, List.flatMap_append,
        List.flatMap_singleton, List.reverse_append, List.map_append, ← List.map_reverse,
        ← List.filter_reverse, List.reverse_reverse, filter_range_lt]
      simp

/-- The marks of vertices `n - 1, …, 0` (top first) for vertex `v`. -/
def mkL (n v : ℕ) : List Bool := ((List.range n).map (· == v)).reverse

theorem walkM_mkL (n v : ℕ) :
    walkM (mkL n v) [] = (pairs n).reverse.map fun p => (p.1 == v, p.2 == v) := by
  have hw := walkM_pairs (· == v) n n le_rfl
  rw [Nat.sub_self, List.range'_zero, List.map_nil] at hw
  exact hw

theorem length_pairs_eq_tri (n : ℕ) : (pairs n).length = tri n := by
  have h := congrArg List.length (walkM_mkL n 0)
  rw [walkM_length] at h
  simpa [mkL] using h.symm

theorem map_range_beq (n w : ℕ) (hw : w < n) :
    (List.range n).map (· == w) =
      List.replicate w false ++ true :: List.replicate (n - 1 - w) false := by
  induction n with
  | zero => omega
  | succ n ih =>
      rw [List.range_succ, List.map_append]
      rcases Nat.lt_or_ge w n with h | h
      · rw [ih h, show n + 1 - 1 - w = n - 1 - w + 1 by omega, List.replicate_succ']
        simp [show n ≠ w by omega]
      · obtain rfl : w = n := by omega
        rw [show (List.range w).map (· == w) = List.replicate w false from
          List.eq_replicate_iff.2 ⟨by simp, fun b hb => by
            obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hb
            simpa using (List.mem_range.1 hj).ne⟩]
        simp

/-- The touch bits a vertex walk computes are `touches`. -/
theorem walk_touches (n : ℕ) (bits : List Bool) (v : ℕ) (hb : bits.length = (pairs n).length) :
    (List.zipWith (fun p b => b && (p.2 || p.1)) (walkM (mkL n v) []) bits.reverse).reverse =
      (List.range (pairs n).length).map (touches n bits v) := by
  rw [walkM_mkL, List.zipWith_map_left, ← List.reverse_zipWith hb.symm, List.reverse_reverse]
  apply List.ext_getElem (by simp [hb])
  intro q h₁ h₂
  rw [List.length_map, List.length_range] at h₂
  rw [List.getElem_zipWith, List.getElem_map, List.getElem_range, touches,
    List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ h₂, Bool.or_comm]

end Cslib.Complexity.Karp.EmitSS
