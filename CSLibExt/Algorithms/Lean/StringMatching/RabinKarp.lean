/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.StringMatching.Naive
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.ZMod.Basic

import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Order.BigOperators.Group.List

/-!
# Rabin-Karp all-occurrence string matching

`rabinKarpMatches` computes pattern and first-window hashes by Horner's rule, then advances two
shared suffix cursors to update each window hash. A hash hit is verified from left to right, so
the result records all exact occurrences, including overlaps and the final alignment.

This is the deterministic stage of CLRS, fourth edition, Section 32.2. It extends the source's
digit and nonempty-pattern domains to arbitrary natural bases and symbols, with positive modulus.
The empty pattern matches every bounded text boundary. Failed bounded initialization returns no
matches for a pattern longer than the text, but retains the initialization work already executed.

The cost counts each executed multiplication, addition, normalized subtraction, modulus, borrow
test, hash equality, and verification symbol equality. Pointer/list operations, offset arithmetic,
other control flow, calls, instrumentation, allocation, and output construction are free. This is
not a full RAM or bit-cost bound. Probability and word/bit refinements remain separate obligations.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

@[no_expose]
private def rkPrefix : List Nat → List Nat → TimeM Nat Bool
  | [], _ => pure true
  | _ :: _, [] => pure false
  | x :: xs, y :: ys => do
      ✓
      if x == y then rkPrefix xs ys else pure false

@[no_expose]
private def rkHigh (d q : Nat) : List Nat → Nat → TimeM Nat Nat
  | [], h => pure h
  | _ :: xs, h => do
      ✓[2]
      rkHigh d q xs ((d * h) % q)

@[no_expose]
private def rkSetup (d q : Nat) : List Nat → List Nat → Nat → Nat →
    TimeM Nat (Option (Nat × Nat × List Nat))
  | [], text, p, t => pure (some (p, t, text))
  | _ :: _, [], _, _ => pure none
  | x :: xs, y :: ys, p, t => do
      ✓[6]
      rkSetup d q xs ys ((d * p + x) % q) ((d * t + y) % q)

@[no_expose]
private def rkRoll (d q h t outgoing incoming : Nat) : TimeM Nat Nat := do
  ✓[2]
  let removed := outgoing * h % q
  ✓
  let cleared ← if t < removed then do
      ✓[2]
      pure (t + q - removed)
    else do
      ✓
      pure (t - removed)
  ✓[3]
  pure ((d * cleared + incoming) % q)

@[no_expose]
private def rkCandidate (pattern outgoing : List Nat) (p t : Nat) : TimeM Nat Bool := do
  ✓
  if p == t then rkPrefix pattern outgoing else pure false

@[no_expose]
private def rkScan (d q h p : Nat) (pattern : List Nat) :
    List Nat → List Nat → Nat → Nat → TimeM Nat (List Nat)
  | outgoing, [], t, offset => do
      let found ← rkCandidate pattern outgoing p t
      pure (if found then [offset] else [])
  | [], _ :: _, _, _ => pure []
  | outgoing :: outgoingTail, incoming :: incomingTail, t, offset => do
      let found ← rkCandidate pattern (outgoing :: outgoingTail) p t
      let next ← rkRoll d q h t outgoing incoming
      let remaining ← rkScan d q h p pattern outgoingTail incomingTail next (offset + 1)
      pure (if found then offset :: remaining else remaining)

@[no_expose]
private def rkBoundaries : List Nat → Nat → List Nat
  | [], offset => [offset]
  | _ :: xs, offset => offset :: rkBoundaries xs (offset + 1)

/-- All exact matching zero-based shifts, with executed arithmetic and equality operation cost. -/
public def rabinKarpMatches (d q : Nat) (pattern text : List Nat) (_hq : 0 < q) :
    TimeM Nat (List Nat) :=
  match pattern with
  | [] => pure (rkBoundaries text 0)
  | _ :: tail => do
      ✓
      let h ← rkHigh d q tail (1 % q)
      let initialized ← rkSetup d q pattern text 0 0
      match initialized with
      | none => pure []
      | some (p, t, incoming) => rkScan d q h p pattern text incoming t 0


@[expose] public section

private lemma rkRoll_ret (d q h t outgoing incoming : Nat) :
    (rkRoll d q h t outgoing incoming).ret =
      (d * (if t < outgoing * h % q then t + q - outgoing * h % q
        else t - outgoing * h % q) + incoming) % q := by
  by_cases hb : t < outgoing * h % q <;> simp [rkRoll, hb]
private lemma rkRoll_lt (d q h t outgoing incoming : Nat) (hq : 0 < q) :
    (rkRoll d q h t outgoing incoming).ret < q := by
  rw [rkRoll_ret]
  exact Nat.mod_lt _ hq

private lemma rkCleared_lt (q h t outgoing : Nat) (hq : 0 < q) (ht : t < q) :
    (if t < outgoing * h % q then t + q - outgoing * h % q
      else t - outgoing * h % q) < q := by
  have hr : outgoing * h % q < q := Nat.mod_lt _ hq
  split <;> omega
private lemma rkCleared_cast (q h t outgoing : Nat) (hq : 0 < q) :
    ((if t < outgoing * h % q then t + q - outgoing * h % q
      else t - outgoing * h % q : Nat) : ZMod q) =
      (t : ZMod q) - outgoing * h := by
  have hr : outgoing * h % q < q := Nat.mod_lt _ hq
  by_cases hb : t < outgoing * h % q
  · have hle : outgoing * h % q ≤ t + q := by omega
    simp only [hb, ↓reduceIte, Nat.cast_sub hle, Nat.cast_add, ZMod.natCast_self, add_zero,
      ZMod.natCast_mod, Nat.cast_mul]
  · have hle : outgoing * h % q ≤ t := by omega
    simp only [hb, ↓reduceIte, Nat.cast_sub hle, ZMod.natCast_mod, Nat.cast_mul]

private lemma rkRoll_cast (d q h t outgoing incoming : Nat) (hq : 0 < q) :
    ((rkRoll d q h t outgoing incoming).ret : ZMod q) =
      (d : ZMod q) * (t - outgoing * h) + incoming := by
  rw [rkRoll_ret]
  simp only [ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul, rkCleared_cast q h t outgoing hq]
private lemma rkRoll_signed (d q h t outgoing incoming : Nat) (hq : 0 < q) :
    ((rkRoll d q h t outgoing incoming).ret : Int) =
      ((d : Int) * (t - outgoing * h) + incoming) % q := by
  let : NeZero q := ⟨Nat.ne_of_gt hq⟩
  have ht := rkRoll_lt d q h t outgoing incoming hq
  have hc := rkRoll_cast d q h t outgoing incoming hq
  have he : ((rkRoll d q h t outgoing incoming).ret : ZMod q) =
      (((d : Int) * (t - outgoing * h) + incoming : Int) : ZMod q) := by
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_sub, Int.cast_natCast] using hc
  have hv := congrArg (fun x : ZMod q => (x.val : Int)) he
  simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt ht, ZMod.val_intCast] using hv


private lemma rkHigh_cast (d q : Nat) (xs : List Nat) (h : Nat) :
    ((rkHigh d q xs h).ret : ZMod q) = (d : ZMod q) ^ xs.length * h := by
  induction xs generalizing h with
  | nil => simp [rkHigh]
  | cons x xs ih =>
      simp only [rkHigh, Cslib.Algorithms.Lean.TimeM.ret_bind,
        ih, List.length_cons,
        ZMod.natCast_mod, Nat.cast_mul, pow_succ, mul_assoc]
private lemma rkHigh_lt (d q : Nat) (xs : List Nat) (h : Nat) (hq : 0 < q) (hh : h < q) :
    (rkHigh d q xs h).ret < q := by
  induction xs generalizing h with
  | nil => exact hh
  | cons x xs ih =>
      simpa only [rkHigh, Cslib.Algorithms.Lean.TimeM.ret_bind] using ih _ (Nat.mod_lt _ hq)
private lemma rkHigh_initial (d q : Nat) (xs : List Nat) (hq : 0 < q) :
    (rkHigh d q xs (1 % q)).ret = d ^ xs.length % q := by
  have he := congrArg ZMod.val (rkHigh_cast d q xs (1 % q))
  simpa only [ZMod.natCast_mod, Nat.cast_one, mul_one, ← Nat.cast_pow, ZMod.val_natCast,
    Nat.mod_eq_of_lt (rkHigh_lt d q xs (1 % q) hq (Nat.mod_lt _ hq))] using he
private lemma rkHigh_time (d q : Nat) (xs : List Nat) (h : Nat) :
    (rkHigh d q xs h).time = 2 * xs.length := by
  induction xs generalizing h with
  | nil => rfl
  | cons x xs ih => simp [rkHigh, ih, Nat.mul_add, Nat.add_comm]

private lemma rkPrefix_ret (pattern text : List Nat) :
    (rkPrefix pattern text).ret = pattern.isPrefixOf text := by
  induction pattern generalizing text with
  | nil => simp [rkPrefix]
  | cons x xs ih =>
      cases text with
      | nil => simp [rkPrefix]
      | cons y ys => cases h : x == y <;> simp [rkPrefix, List.isPrefixOf, h, ih]
private lemma rkPrefix_time (pattern text : List Nat) (hlen : pattern.length ≤ text.length) :
    (rkPrefix pattern text).time =
      min pattern.length ((pattern.zip text).findIdx (fun pair => !(pair.1 == pair.2)) + 1) := by
  induction pattern generalizing text with
  | nil => simp [rkPrefix]
  | cons x xs ih =>
      cases text with
      | nil => simp at hlen
      | cons y ys =>
          have htail : xs.length ≤ ys.length := by simpa using hlen
          cases h : x == y with
          | false => simp [rkPrefix, h, List.findIdx_cons]
          | true =>
              simp only [rkPrefix, h, ↓reduceIte, Cslib.Algorithms.Lean.TimeM.time_bind,
                Cslib.Algorithms.Lean.TimeM.time_tick, List.zip_cons_cons, List.findIdx_cons,
                Bool.not_true, Bool.false_eq_true, List.length_cons, ↓reduceIte]
              rw [ih ys htail]
              omega

private lemma rkRadix_horner (d q p x : Nat) (xs : List Nat) :
    (d ^ xs.length * ((d * p + x) % q) + Nat.ofDigits d xs.reverse) % q =
      (d ^ (xs.length + 1) * p + Nat.ofDigits d (x :: xs).reverse) % q := by
  have hc : (((d ^ xs.length * ((d * p + x) % q) + Nat.ofDigits d xs.reverse) % q : Nat) :
      ZMod q) = ((d ^ (xs.length + 1) * p + Nat.ofDigits d (x :: xs).reverse) % q : Nat) := by
    rw [Nat.ofDigits_reverse_cons]
    simp only [ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, pow_succ]
    ring
  have hv := congrArg ZMod.val hc
  simpa only [ZMod.val_natCast, Nat.mod_mod] using hv

private lemma rkSetup_ret (d q : Nat) (pattern text : List Nat) (p t : Nat)
    (hq : 0 < q) (hp : p < q) (ht : t < q) :
    (rkSetup d q pattern text p t).ret =
      if pattern.length ≤ text.length then
        some ((d ^ pattern.length * p + Nat.ofDigits d pattern.reverse) % q,
          (d ^ pattern.length * t + Nat.ofDigits d (text.take pattern.length).reverse) % q,
          text.drop pattern.length)
      else none := by
  induction pattern generalizing text p t with
  | nil => simp [rkSetup, Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt ht]
  | cons x xs ih =>
      cases text with
      | nil => simp [rkSetup]
      | cons y ys =>
          simp only [rkSetup, Cslib.Algorithms.Lean.TimeM.ret_bind]
          rw [ih ys _ _ (Nat.mod_lt _ hq) (Nat.mod_lt _ hq)]
          by_cases hlen : xs.length ≤ ys.length
          · simp only [hlen, ↓reduceIte, List.length_cons, Nat.succ_le_succ_iff,
              List.take_succ_cons, List.drop_succ_cons]
            rw [rkRadix_horner]
            have he := rkRadix_horner d q t y (ys.take xs.length)
            have hl : (ys.take xs.length).length = xs.length := List.length_take_of_le hlen
            simp only [hl] at he
            rw [he]
          · simp [hlen]


private lemma rkRoll_window (d q outgoing incoming : Nat) (middle : List Nat) (hq : 0 < q) :
    (rkRoll d q (d ^ middle.length % q)
      (Nat.ofDigits d (outgoing :: middle).reverse % q) outgoing incoming).ret =
      Nat.ofDigits d (middle ++ [incoming]).reverse % q := by
  have hn : Nat.ofDigits d (middle ++ [incoming]).reverse =
      d * Nat.ofDigits d middle.reverse + incoming := by
    simp [Nat.ofDigits_cons, Nat.add_comm]
  have hc : ((rkRoll d q (d ^ middle.length % q)
      (Nat.ofDigits d (outgoing :: middle).reverse % q) outgoing incoming).ret : ZMod q) =
      Nat.ofDigits d (middle ++ [incoming]).reverse := by
    rw [rkRoll_cast d q _ _ outgoing incoming hq, hn, Nat.ofDigits_reverse_cons]
    simp only [ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
    ring
  have hv := congrArg ZMod.val hc
  simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt (rkRoll_lt d q _ _ outgoing incoming hq)]
    using hv

private lemma rkCandidate_ret (pattern outgoing : List Nat) (p t : Nat)
    (hhash : pattern.isPrefixOf outgoing = true → p = t) :
    (rkCandidate pattern outgoing p t).ret = pattern.isPrefixOf outgoing := by
  cases hprefix : pattern.isPrefixOf outgoing with
  | false =>
      by_cases he : p = t <;> simp [rkCandidate, he, rkPrefix_ret, hprefix]
  | true => simp [rkCandidate, rkPrefix_ret, hprefix, hhash hprefix]
private lemma rkCandidate_front (d q : Nat) (pattern front incoming : List Nat)
    (hlen : pattern.length = front.length) :
    (rkCandidate pattern (front ++ incoming) (Nat.ofDigits d pattern.reverse % q)
      (Nat.ofDigits d front.reverse % q)).ret = pattern.isPrefixOf (front ++ incoming) := by
  apply rkCandidate_ret
  intro hprefix
  have he := List.prefix_iff_eq_take.mp (List.isPrefixOf_iff_prefix.mp hprefix)
  have hf : pattern = front := by simpa [hlen] using he
  rw [hf]

private lemma rkScan_ret (d q : Nat) (pattern front incoming : List Nat) (offset : Nat)
    (hq : 0 < q) (hpos : 0 < pattern.length) (hlen : pattern.length = front.length) :
    (rkScan d q (d ^ (pattern.length - 1) % q) (Nat.ofDigits d pattern.reverse % q) pattern
      (front ++ incoming) incoming (Nat.ofDigits d front.reverse % q) offset).ret =
      ((front ++ incoming).tails.take (incoming.length + 1)).findIdxs pattern.isPrefixOf
        offset := by
  induction incoming generalizing front offset with
  | nil =>
      have hc := rkCandidate_front d q pattern front [] hlen
      cases front with
      | nil =>
          have hf : pattern.length = 0 := hlen
          omega
      | cons x xs =>
          simp only [List.append_nil] at hc
          simp only [List.append_nil, rkScan, ret_bind,
            ret_pure]
          rw [hc]
          simp
  | cons y ys ih =>
      cases front with
      | nil =>
          have hf : pattern.length = 0 := hlen
          omega
      | cons x xs =>
          have hexp : pattern.length - 1 = xs.length := by
            simp only [List.length_cons] at hlen
            omega
          have hn : pattern.length = (xs ++ [y]).length := by simpa using hlen
          have hc := rkCandidate_front d q pattern (x :: xs) (y :: ys) hlen
          have hr := ih (xs ++ [y]) (offset + 1) hn
          simp only [hexp, List.append_assoc, List.singleton_append] at hr
          simp only [List.cons_append, rkScan, ret_bind,
            ret_pure, hexp, rkRoll_window d q x y xs hq]
          simp only [List.cons_append] at hc
          rw [hc, hr]
          simp

private lemma rkBoundaries_eq (text : List Nat) (offset : Nat) :
    rkBoundaries text offset = List.range' offset (text.length + 1) := by
  induction text generalizing offset with
  | nil => simp [rkBoundaries, List.range'_succ]
  | cons x xs ih => simp [rkBoundaries, ih, List.range'_succ]

/-- Erasing cost gives the same all-occurrence result as canonical naive matching. -/
theorem rabinKarpMatches_ret_eq_naiveMatches (d q : Nat) (pattern text : List Nat) (hq : 0 < q) :
    (rabinKarpMatches d q pattern text hq).ret = (naiveMatches pattern text).ret := by
  cases pattern with
  | nil =>
      simp [rabinKarpMatches, rkBoundaries_eq, naiveMatches_nil_pattern, List.range_eq_range']
  | cons x xs =>
      simp only [rabinKarpMatches, ret_bind]
      rw [rkSetup_ret d q (x :: xs) text 0 0 hq hq hq]
      by_cases hlen : (x :: xs).length ≤ text.length
      · simp only [hlen, ↓reduceIte, Nat.mul_zero, Nat.zero_add]
        rw [rkHigh_initial d q xs hq]
        have hf : (x :: xs).length = (text.take (x :: xs).length).length :=
          (List.length_take_of_le hlen).symm
        have hs := rkScan_ret d q (x :: xs) (text.take (x :: xs).length)
          (text.drop (x :: xs).length) 0 hq (by simp) hf
        rw [List.take_append_drop] at hs
        simp only [naiveMatches_ret, hlen, ↓reduceIte]
        simpa only [List.length_drop, List.length_cons, Nat.add_sub_cancel]
          using hs
      · simp only [naiveMatches_ret, hlen, ↓reduceIte, ret_pure]


private lemma rkSetup_time (d q : Nat) (pattern text : List Nat) (p t : Nat) :
    (rkSetup d q pattern text p t).time = 6 * min pattern.length text.length := by
  induction pattern generalizing text p t with
  | nil => simp [rkSetup]
  | cons x xs ih =>
      cases text with
      | nil => simp [rkSetup]
      | cons y ys => simp [rkSetup, ih, Nat.mul_add, Nat.add_comm]
private lemma rkRoll_time (d q h t outgoing incoming : Nat) :
    (rkRoll d q h t outgoing incoming).time = 7 + if t < outgoing * h % q then 1 else 0 := by
  by_cases hb : t < outgoing * h % q <;> simp [rkRoll, hb]
private lemma rkCandidate_time (pattern outgoing : List Nat) (p t : Nat)
    (hlen : pattern.length ≤ outgoing.length) :
    (rkCandidate pattern outgoing p t).time = 1 +
      if p = t then min pattern.length
        ((pattern.zip outgoing).findIdx (fun pair => !(pair.1 == pair.2)) + 1) else 0 := by
  by_cases hh : p = t <;> simp [rkCandidate, hh, rkPrefix_time pattern outgoing hlen]

private lemma rkScan_time (d q : Nat) (pattern front incoming : List Nat) (offset : Nat)
    (hq : 0 < q) (hpos : 0 < pattern.length) (hlen : pattern.length = front.length) :
    let candidateCost := fun suffix : List Nat => 1 +
      if Nat.ofDigits d pattern.reverse % q =
          Nat.ofDigits d (suffix.take pattern.length).reverse % q then
        min pattern.length ((pattern.zip suffix).findIdx (fun pair => !(pair.1 == pair.2)) + 1)
      else 0
    let rollingCost := fun suffix : List Nat => 7 +
      if Nat.ofDigits d (suffix.take pattern.length).reverse % q <
          suffix.head! * (d ^ (pattern.length - 1) % q) % q then 1 else 0
    (rkScan d q (d ^ (pattern.length - 1) % q) (Nat.ofDigits d pattern.reverse % q) pattern
      (front ++ incoming) incoming (Nat.ofDigits d front.reverse % q) offset).time =
      (((front ++ incoming).tails.take (incoming.length + 1)).map candidateCost).sum +
        (((front ++ incoming).tails.take incoming.length).map rollingCost).sum := by
  dsimp only
  induction incoming generalizing front offset with
  | nil =>
      cases front with
      | nil =>
          have hf : pattern.length = 0 := hlen
          omega
      | cons x xs =>
          have hc := rkCandidate_time pattern (x :: xs) (Nat.ofDigits d pattern.reverse % q)
            (Nat.ofDigits d (x :: xs).reverse % q) (by omega)
          simp only [List.append_nil, rkScan, time_bind,
            time_pure, Nat.add_zero]
          rw [hc]
          simp [hlen]
  | cons y ys ih =>
      cases front with
      | nil =>
          have hf : pattern.length = 0 := hlen
          omega
      | cons x xs =>
          have hexp : pattern.length - 1 = xs.length := by
            simp only [List.length_cons] at hlen
            omega
          have hn : pattern.length = (xs ++ [y]).length := by simpa using hlen
          have hc := rkCandidate_time pattern ((x :: xs) ++ y :: ys)
            (Nat.ofDigits d pattern.reverse % q) (Nat.ofDigits d (x :: xs).reverse % q)
            (by simp only [List.length_append, List.length_cons]; omega)
          have hr := ih (xs ++ [y]) (offset + 1) hn
          simp only [hexp, List.append_assoc, List.singleton_append] at hr
          simp only [List.cons_append, rkScan, time_bind,
            time_pure, Nat.add_zero, hexp,
            rkRoll_window d q x y xs hq]
          simp only [List.cons_append] at hc
          rw [hc, hr, rkRoll_time]
          simp [hlen, List.take_append]
          omega

private lemma rkMatches_time_phase (d q : Nat) (pattern text : List Nat) (hq : 0 < q)
    (hpos : 0 < pattern.length) (hlen : pattern.length ≤ text.length) :
    (rabinKarpMatches d q pattern text hq).time = 8 * pattern.length - 1 +
      (rkScan d q (d ^ (pattern.length - 1) % q) (Nat.ofDigits d pattern.reverse % q) pattern
        text (text.drop pattern.length)
        (Nat.ofDigits d (text.take pattern.length).reverse % q) 0).time := by
  cases pattern with
  | nil => simp at hpos
  | cons x xs =>
      simp only [rabinKarpMatches, time_bind, time_tick]
      rw [rkSetup_ret d q (x :: xs) text 0 0 hq hq hq]
      simp only [hlen, ↓reduceIte, Nat.mul_zero, Nat.zero_add]
      rw [rkHigh_time, rkHigh_initial d q xs hq, rkSetup_time, Nat.min_eq_left hlen]
      simp only [List.length_cons, Nat.add_sub_cancel]
      omega

/-- Exact setup, hash tests, rolling work, borrow additions, and hit-verification cost. -/
theorem rabinKarpMatches_time_eq (d q : Nat) (pattern text : List Nat) (hq : 0 < q)
    (hpos : 0 < pattern.length) (hlen : pattern.length ≤ text.length) :
    let m := pattern.length
    let r := text.length - m
    let residue := fun suffix : List Nat => Nat.ofDigits d (suffix.take m).reverse % q
    let borrows := ((text.tails.take r).map fun suffix =>
      if residue suffix < suffix.head! * (d ^ (m - 1) % q) % q then 1 else 0).sum
    let verification := ((text.tails.take (r + 1)).map fun suffix =>
      if Nat.ofDigits d pattern.reverse % q = residue suffix then
        min m ((pattern.zip suffix).findIdx (fun pair => !(pair.1 == pair.2)) + 1) else 0).sum
    (rabinKarpMatches d q pattern text hq).time =
      (8 * m - 1) + (r + 1) + 7 * r + borrows + verification := by
  dsimp only
  rw [rkMatches_time_phase d q pattern text hq hpos hlen]
  have hf : pattern.length = (text.take pattern.length).length :=
    (List.length_take_of_le hlen).symm
  have hs := rkScan_time d q pattern (text.take pattern.length) (text.drop pattern.length)
    0 hq hpos hf
  rw [List.take_append_drop] at hs
  simp only [List.length_drop] at hs
  rw [hs]
  simp only [List.sum_map_add]
  simp
  omega


/-- An offset is reported exactly when the canonical pattern match holds there. -/
theorem mem_rabinKarpMatches_iff (d q : Nat) (pattern text : List Nat) (hq : 0 < q) (offset : Nat) :
    offset ∈ (rabinKarpMatches d q pattern text hq).ret ↔
      Cslib.Algorithms.Lean.StringMatching.MatchAt pattern text offset := by
  rw [rabinKarpMatches_ret_eq_naiveMatches]
  exact mem_naiveMatches_iff pattern text offset
/-- Reported offsets are strictly increasing, so overlapping occurrences are never duplicated. -/
theorem rabinKarpMatches_pairwise (d q : Nat) (pattern text : List Nat) (hq : 0 < q) :
    (rabinKarpMatches d q pattern text hq).ret.Pairwise (· < ·) := by
  rw [rabinKarpMatches_ret_eq_naiveMatches]
  exact naiveMatches_pairwise pattern text
/-- The empty pattern matches every bounded text boundary, with zero counted operations. -/
@[simp]
theorem rabinKarpMatches_nil_pattern (d q : Nat) (text : List Nat) (hq : 0 < q) :
    rabinKarpMatches d q [] text hq = ⟨List.range (text.length + 1), 0⟩ := by
  apply TimeM.ext
  · rw [rabinKarpMatches_ret_eq_naiveMatches, naiveMatches_nil_pattern]
  · rfl

private lemma rkSum_hit_le {α : Type} (xs : List α) (p : α → Bool) (f : α → Nat) (m : Nat)
    (hf : ∀ x ∈ xs, f x ≤ m) :
    (xs.map (fun x => if p x then f x else 0)).sum ≤ m * xs.countP p := by
  calc
    (xs.map (fun x => if p x then f x else 0)).sum ≤
        (xs.map (fun x => if p x then m else 0)).sum := by
      apply List.sum_le_sum
      intro x hx
      split
      · exact hf x hx
      · exact Nat.le_refl 0
    _ = m * xs.countP p := by
      rw [List.sum_map_ite]
      simp [List.countP_eq_length_filter, Nat.mul_comm]

/-- Setup plus matching work is bounded by the candidate count and the number of hash hits. -/
theorem rabinKarpMatches_time_le (d q : Nat) (pattern text : List Nat) (hq : 0 < q)
    (hpos : 0 < pattern.length) (hlen : pattern.length ≤ text.length) :
    let m := pattern.length
    let r := text.length - m
    let hashHits := (text.tails.take (r + 1)).countP fun suffix =>
      Nat.ofDigits d pattern.reverse % q == Nat.ofDigits d (suffix.take m).reverse % q
    (rabinKarpMatches d q pattern text hq).time ≤
      (8 * m - 1) + (9 * (r + 1) - 8) + m * hashHits := by
  dsimp only
  rw [rabinKarpMatches_time_eq d q pattern text hq hpos hlen]
  dsimp only
  have hb : ((text.tails.take (text.length - pattern.length)).map fun suffix =>
      if Nat.ofDigits d (suffix.take pattern.length).reverse % q <
          suffix.head! * (d ^ (pattern.length - 1) % q) % q then 1 else 0).sum ≤
      text.length - pattern.length := by
    have he := List.sum_le_length_nsmul
      ((text.tails.take (text.length - pattern.length)).map fun suffix =>
        if Nat.ofDigits d (suffix.take pattern.length).reverse % q <
            suffix.head! * (d ^ (pattern.length - 1) % q) % q then 1 else 0) 1 (by
          intro value hv
          obtain ⟨suffix, _, rfl⟩ := List.mem_map.mp hv
          split <;> omega)
    exact he.trans (by simp)
  have hv := rkSum_hit_le (text.tails.take (text.length - pattern.length + 1))
    (fun suffix => Nat.ofDigits d pattern.reverse % q ==
      Nat.ofDigits d (suffix.take pattern.length).reverse % q)
    (fun suffix => min pattern.length
      ((pattern.zip suffix).findIdx (fun pair => !(pair.1 == pair.2)) + 1))
    pattern.length (by
      intro suffix _
      exact Nat.min_le_left _ _)
  simp only [beq_iff_eq] at hv
  omega

/-- Overlength patterns return no matches, retaining high-place and attempted Horner setup costs. -/
@[simp]
theorem rabinKarpMatches_of_length_lt (d q : Nat) (pattern text : List Nat) (hq : 0 < q)
    (hlen : text.length < pattern.length) :
    rabinKarpMatches d q pattern text hq =
      ⟨[], 1 + 2 * (pattern.length - 1) + 6 * text.length⟩ := by
  apply TimeM.ext
  · rw [rabinKarpMatches_ret_eq_naiveMatches, naiveMatches_of_length_lt pattern text hlen]
    rfl
  · cases pattern with
    | nil => simp at hlen
    | cons x xs =>
        have hnot : ¬(x :: xs).length ≤ text.length := by omega
        simp only [rabinKarpMatches, time_bind, time_tick]
        rw [rkSetup_ret d q (x :: xs) text 0 0 hq hq hq]
        simp only [hnot, ↓reduceIte, time_pure, Nat.add_zero]
        rw [rkHigh_time, rkSetup_time, Nat.min_eq_right (Nat.le_of_lt hlen)]
        simp [Nat.add_assoc]


private lemma rkSuffix_replicate (a m n c : Nat) (suffix : List Nat) (hmn : m ≤ n)
    (hc : c ≤ n - m + 1) (hs : suffix ∈ (List.replicate n a).tails.take c) :
    ∃ k, m ≤ k ∧ suffix = List.replicate k a := by
  obtain ⟨offset, hoffset, rfl⟩ := List.mem_iff_getElem.mp hs
  have ho : offset < c := by
    have hm : c ≤ (List.replicate n a).tails.length := by simp; omega
    simpa only [List.length_take_of_le hm] using hoffset
  refine ⟨n - offset, by omega, ?_⟩
  simp [List.drop_replicate]
private lemma rkPrefix_replicate (a m n : Nat) (hlen : m ≤ n) :
    rkPrefix (List.replicate m a) (List.replicate n a) = ⟨true, m⟩ := by
  induction m generalizing n with
  | zero => rfl
  | succ m ih =>
      cases n with
      | zero => omega
      | succ n =>
          have htail : m ≤ n := by omega
          apply TimeM.ext
          · simp [List.replicate_succ, rkPrefix, ih n htail]
          · simp [List.replicate_succ, rkPrefix, ih n htail, Nat.add_comm]

private lemma rkReplicate_verification (d q a m n : Nat) (hlen : m ≤ n) :
    (((List.replicate n a).tails.take (n - m + 1)).map fun suffix =>
      if Nat.ofDigits d (List.replicate m a).reverse % q =
          Nat.ofDigits d (suffix.take m).reverse % q then
        min m (((List.replicate m a).zip suffix).findIdx
          (fun pair => !(pair.1 == pair.2)) + 1) else 0).sum = m * (n - m + 1) := by
  have he := List.sum_eq_length_nsmul
    (((List.replicate n a).tails.take (n - m + 1)).map fun suffix =>
      if Nat.ofDigits d (List.replicate m a).reverse % q =
          Nat.ofDigits d (suffix.take m).reverse % q then
        min m (((List.replicate m a).zip suffix).findIdx
          (fun pair => !(pair.1 == pair.2)) + 1) else 0) m (by
      intro value hv
      obtain ⟨suffix, hs, rfl⟩ := List.mem_map.mp hv
      obtain ⟨k, hk, rfl⟩ := rkSuffix_replicate a m n (n - m + 1) suffix hlen (by omega) hs
      simp only [List.take_replicate, Nat.min_eq_left hk, ↓reduceIte]
      have hp := rkPrefix_time (List.replicate m a) (List.replicate k a) (by simpa using hk)
      rw [rkPrefix_replicate a m k hk] at hp
      simpa using hp.symm)
  simpa [Nat.mul_comm] using he

private lemma rkReplicate_borrows (d q a m n : Nat) (hpos : 0 < m) (hlen : m ≤ n) :
    (((List.replicate n a).tails.take (n - m)).map fun suffix =>
      if Nat.ofDigits d (suffix.take m).reverse % q <
          suffix.head! * (d ^ (m - 1) % q) % q then 1 else 0).sum =
      (n - m) * if Nat.ofDigits d (List.replicate m a).reverse % q <
        a * (d ^ (m - 1) % q) % q then 1 else 0 := by
  have he := List.sum_eq_length_nsmul
    (((List.replicate n a).tails.take (n - m)).map fun suffix =>
      if Nat.ofDigits d (suffix.take m).reverse % q <
          suffix.head! * (d ^ (m - 1) % q) % q then 1 else 0)
    (if Nat.ofDigits d (List.replicate m a).reverse % q <
      a * (d ^ (m - 1) % q) % q then 1 else 0) (by
        intro value hv
        obtain ⟨suffix, hs, rfl⟩ := List.mem_map.mp hv
        obtain ⟨k, hk, rfl⟩ := rkSuffix_replicate a m n (n - m) suffix hlen (by omega) hs
        have hh : (List.replicate k a).head! = a := by
          cases k with
          | zero => omega
          | succ k => simp [List.replicate_succ]
        simp only [List.take_replicate, Nat.min_eq_left hk, hh])
  have hc : n - m ≤ n + 1 := by omega
  simpa [Nat.min_eq_left hc] using he

/-- Repeated-symbol words execute exactly m comparisons at every alignment, plus setup and rolls. -/
theorem rabinKarpMatches_time_replicate (d q a m n : Nat) (hq : 0 < q) (hpos : 0 < m)
    (hlen : m ≤ n) :
    let t := Nat.ofDigits d (List.replicate m a).reverse % q
    let borrow := if t < a * (d ^ (m - 1) % q) % q then 1 else 0
    (rabinKarpMatches d q (List.replicate m a) (List.replicate n a) hq).time =
      (8 * m - 1) + (n - m + 1) + 7 * (n - m) +
        (n - m) * borrow + m * (n - m + 1) := by
  have he := rabinKarpMatches_time_eq d q (List.replicate m a) (List.replicate n a) hq
    (by simpa using hpos) (by simpa using hlen)
  dsimp only at he ⊢
  simp only [List.length_replicate] at he
  rw [rkReplicate_borrows d q a m n hpos hlen, rkReplicate_verification d q a m n hlen] at he
  exact he
/-- Repeated-symbol words report every possible shift, including overlaps. -/
theorem rabinKarpMatches_ret_replicate (d q a m n : Nat) (hq : 0 < q) (hlen : m ≤ n) :
    (rabinKarpMatches d q (List.replicate m a) (List.replicate n a) hq).ret =
      List.range (n - m + 1) := by
  rw [rabinKarpMatches_ret_eq_naiveMatches]
  exact Cslib.Algorithms.Lean.TimeM.naiveMatches_ret_replicate a m n hlen

/-- Repeated-symbol matching cost lies between mL and 10mL, independently of preprocessing. -/
theorem rabinKarpMatches_matching_time_replicate (d q a m n : Nat) (hq : 0 < q)
    (hpos : 0 < m) (hlen : m ≤ n) :
    let matchingCost := (rabinKarpMatches d q (List.replicate m a)
      (List.replicate n a) hq).time - (8 * m - 1)
    m * (n - m + 1) ≤ matchingCost ∧ matchingCost ≤ 10 * (m * (n - m + 1)) := by
  have hl : n - m + 1 ≤ m * (n - m + 1) := by
    have he := Nat.mul_le_mul_right (n - m + 1) (show 1 ≤ m by omega)
    simpa using he
  dsimp only
  rw [rabinKarpMatches_time_replicate d q a m n hq hpos hlen]
  split <;> omega

end

end Cslib.Algorithms.Lean.TimeM
