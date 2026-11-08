/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.StringMatching.RabinKarp

@[expose] public section

set_option autoImplicit false

open Cslib.Algorithms.Lean.StringMatching
open Cslib.Algorithms.Lean.TimeM

example (d q : Nat) (pattern text : List Nat) (hq : 0 < q) :
    (rabinKarpMatches d q pattern text hq).ret = (naiveMatches pattern text).ret :=
  rabinKarpMatches_ret_eq_naiveMatches d q pattern text hq

example (d q : Nat) (pattern text : List Nat) (hq : 0 < q) (offset : Nat) :
    offset ∈ (rabinKarpMatches d q pattern text hq).ret ↔ MatchAt pattern text offset :=
  mem_rabinKarpMatches_iff d q pattern text hq offset

example (d q : Nat) (pattern text : List Nat) (hq : 0 < q) :
    (rabinKarpMatches d q pattern text hq).ret.Pairwise (· < ·) :=
  rabinKarpMatches_pairwise d q pattern text hq

example (d q : Nat) (text : List Nat) (hq : 0 < q) :
    rabinKarpMatches d q [] text hq = ⟨List.range (text.length + 1), 0⟩ :=
  rabinKarpMatches_nil_pattern d q text hq

example (d q : Nat) (pattern text : List Nat) (hq : 0 < q)
    (hlen : text.length < pattern.length) :
    rabinKarpMatches d q pattern text hq =
      ⟨[], 1 + 2 * (pattern.length - 1) + 6 * text.length⟩ :=
  rabinKarpMatches_of_length_lt d q pattern text hq hlen

example : (rabinKarpMatches 10 13 [0, 0, 1, 1, 2] [3, 0, 0, 1, 1, 2] (by decide)).ret =
    [1] := by
  rw [rabinKarpMatches_ret_eq_naiveMatches, naiveMatches_ret]
  decide

example : (rabinKarpMatches 10 13 [0, 0, 1, 1, 2] [3, 0, 0, 1, 1, 2] (by decide)).time =
    54 := by
  rw [rabinKarpMatches_time_eq _ _ _ _ _ (by decide) (by decide)]
  decide

example : (rabinKarpMatches 10 1 [1, 2] [9, 9, 9] (by decide)).time = 26 := by
  rw [rabinKarpMatches_time_eq _ _ _ _ _ (by decide) (by decide)]
  decide

example : (rabinKarpMatches 10 13 [1, 1] [1, 1, 1] (by decide)).ret = [0, 1] := by
  rw [rabinKarpMatches_ret_eq_naiveMatches, naiveMatches_ret]
  decide

example (d q : Nat) (pattern text : List Nat) (hq : 0 < q)
    (hpos : 0 < pattern.length) (hlen : pattern.length ≤ text.length) :
    let m := pattern.length
    let r := text.length - m
    let hashHits := (text.tails.take (r + 1)).countP fun suffix =>
      Nat.ofDigits d pattern.reverse % q == Nat.ofDigits d (suffix.take m).reverse % q
    (rabinKarpMatches d q pattern text hq).time ≤
      (8 * m - 1) + (9 * (r + 1) - 8) + m * hashHits :=
  rabinKarpMatches_time_le d q pattern text hq hpos hlen

example (d q a m n : Nat) (hq : 0 < q) (hlen : m ≤ n) :
    (rabinKarpMatches d q (List.replicate m a) (List.replicate n a) hq).ret =
      List.range (n - m + 1) :=
  rabinKarpMatches_ret_replicate d q a m n hq hlen

example (d q a m n : Nat) (hq : 0 < q) (hpos : 0 < m) (hlen : m ≤ n) :
    let t := Nat.ofDigits d (List.replicate m a).reverse % q
    let borrow := if t < a * (d ^ (m - 1) % q) % q then 1 else 0
    (rabinKarpMatches d q (List.replicate m a) (List.replicate n a) hq).time =
      (8 * m - 1) + (n - m + 1) + 7 * (n - m) +
        (n - m) * borrow + m * (n - m + 1) :=
  rabinKarpMatches_time_replicate d q a m n hq hpos hlen

example (d q a m n : Nat) (hq : 0 < q) (hpos : 0 < m) (hlen : m ≤ n) :
    let matchingCost := (rabinKarpMatches d q (List.replicate m a)
      (List.replicate n a) hq).time - (8 * m - 1)
    m * (n - m + 1) ≤ matchingCost ∧ matchingCost ≤ 10 * (m * (n - m + 1)) :=
  rabinKarpMatches_matching_time_replicate d q a m n hq hpos hlen

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check Cslib.Algorithms.Lean.TimeM.rkPrefix

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check Cslib.Algorithms.Lean.TimeM.rkHigh

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check Cslib.Algorithms.Lean.TimeM.rkSetup

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check Cslib.Algorithms.Lean.TimeM.rkRoll

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check Cslib.Algorithms.Lean.TimeM.rkCandidate

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check Cslib.Algorithms.Lean.TimeM.rkScan

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check Cslib.Algorithms.Lean.TimeM.rkBoundaries

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check Cslib.Algorithms.Lean.TimeM.rkCleared_cast

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check Cslib.Algorithms.Lean.TimeM.rkRoll_cast

/-- error: Unknown -/
#guard_msgs (error, substring := true) in
#check Cslib.Algorithms.Lean.TimeM.rkRoll_signed

/-- error: Tactic `decide` proved -/
#guard_msgs (error, substring := true) in
#check rabinKarpMatches 10 0 [1] [1] (by decide)

end
