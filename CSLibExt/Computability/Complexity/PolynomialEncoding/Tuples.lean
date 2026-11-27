/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.PolynomialEncoding.Represented

/-!
# Polynomial-time enumeration of bounded-length tuples

For a fixed maximum tuple length, each additional coordinate adds one list
comprehension. The input may provide any finite list of choices.
-/

@[expose] public section

namespace Cslib.Complexity.PolynomialEncoding.Comprehension

open MetaMathlibExt.BitstringEncoding

local notation "Word" => List Bool

/-- Lists of at most the specified length having entries from the given list. -/
def tuples {V : Type} (xs : List V) : ℕ → List (List V)
  | 0 => [[]]
  | d + 1 => [] :: xs.flatMap (fun x => (tuples xs d).map (x :: ·))

theorem mem_tuples {V : Type} {xs t : List V} {d : ℕ} :
    t ∈ tuples xs d ↔ t.length ≤ d ∧ ∀ a ∈ t, a ∈ xs := by
  induction d generalizing t with
  | zero => cases t <;> simp [tuples]
  | succ d ih =>
    cases t with
    | nil => simp [tuples]
    | cons v t =>
      simp [tuples, ih, List.mem_flatMap, List.mem_map]
      grind

theorem length_tuples_le {V : Type} (xs : List V) (d : ℕ) :
    (tuples xs d).length ≤ (xs.length + 1) ^ d := by
  induction d with
  | zero => simp [tuples]
  | succ d ih =>
    simp only [tuples, List.length_cons, List.length_flatMap, List.length_map,
      List.map_const', List.length_map, List.sum_replicate_nat, pow_succ]
    nlinarith only [Nat.mul_le_mul_left xs.length ih, Nat.one_le_pow d (xs.length + 1) (by omega)]

namespace Represented

variable {α β γ : Type} {e : α → Word} {r : β → Word} {t : γ → Word}

/-- Concatenate the represented row lists produced by a comprehension. -/
theorem flatMapRows {rows : α → List β} {body : β × α → List γ}
    (rs : Represented e (fun x => frames r (rows x)))
    (bs : Represented (pair r e) (fun p => frames t (body p))) :
    Represented e (fun a => frames t ((rows a).flatMap fun b => body (b, a))) := by
  apply (rs.flatMap bs).transport
  intro a
  simp only [frames, List.map_flatMap, List.flatMap_assoc, List.flatMap_map]

/-- Build all bounded-length tuples on the encoded list of choices. -/
theorem boundedTuples {rows : α → List β} (rs : Represented e (fun x => frames r (rows x)))
    (d : ℕ) : Represented e (fun x => frames (frames r) (tuples (rows x) d)) := by
  induction d with
  | zero => exact const _ (delimit [])
  | succ d ih =>
    let ctx := pair r e
    have tail := (input (frames r)).fst ctx
    have head := ((input r).fst e).snd (frames r)
    have consRow := (head.frame.append tail).transport (g := fun p => frames r (p.2.1 :: p.1))
      (fun _ => rfl)
    have more := rs.flatMapRows ((ih.snd r).mapped consRow)
    exact (const e (delimit [])).append more

end Represented

end Cslib.Complexity.PolynomialEncoding.Comprehension
