/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.PolynomialEncoding.BitScan
public import CSLibExt.Computability.Complexity.BoolClosure
import CSLibExt.Computability.Complexity.PairEncodingConverter

/-!
# Polynomial-time operations on canonically encoded bitstrings

These closure lemmas combine and project computed bitstrings, concatenate
them, and add a self-delimiting frame on the TM2 time model.
-/

@[expose] public section

namespace Cslib.Complexity.PolynomialEncoding.BitScan

open MetaMathlibExt ComplexityTheory BitstringEncoding

local notation "Bits" => List Bool

/-- Copy an arbitrary bitstring. -/
theorem polyWordId : IsPolyTime (fun x : Bits => x) := by
  let step (_ : Unit) (b : Bool) : Unit × Bits := ((), [b])
  have same (x : Bits) : scan step (fun _ => []) () x = x := by
    induction x with
    | nil => rfl
    | cons b x ih => exact congrArg (b :: ·) ih
  exact (funext same) ▸ polyScan step (fun _ => []) ()

/-- Pair two polynomial-time outputs on the same input. -/
theorem polyPair {f g : Bits → Bits} (hf : IsPolyTime f) (hg : IsPolyTime g) :
    IsPolyTime (fun x => (f x, g x)) :=
  ((isPolyTime_dup.comp hg.map_fst).comp isPolyTime_swap).comp hf.map_fst

/-- Transfer a raw-string computation to encoded inputs and outputs. -/
theorem polyEncoded {α β : Type} [BitstringEncoding α] [BitstringEncoding β]
    {f : Bits → Bits} (hf : IsPolyTime f) {g : α → β}
    (he : ∀ a, f (bitEncode a) = bitEncode (g a)) : IsPolyTime g := by
  obtain ⟨m⟩ := Preimage.raw_computable hf
  refine ⟨{ m with outputsFun := fun a => ?_ }⟩
  have h := m.outputsFun (bitEncode a)
  simp only [he] at h
  exact h

/-- Read the first delimited field, then copy the suffix. Each output can be enabled separately. -/
def splitStep (left right : Bool) : Option Bool → Bool → Option Bool × Bits
  | none, b => (none, if right then [b] else [])
  | some false, b => (if b then some true else none, [])
  | some true, b => (some false, if left then [b] else [])

/-- Scan the first delimited field and the remaining suffix, retaining the selected fields. -/
def field (left right : Bool) := scan (splitStep left right) (fun _ => []) (some false)

theorem polyField (left right : Bool) : IsPolyTime (field left right) :=
  polyScan _ _ _

theorem field_delimit (left right : Bool) (p r : Bits) :
    field left right (delimit p ++ r) = (if left then p else []) ++ (if right then r else []) := by
  have tail : scan (splitStep left right) (fun _ => []) none r = if right then r else [] := by
    induction r with
    | nil => cases right <;> rfl
    | cons b r ih => cases right <;> simp_all [scan, splitStep]
  induction p with
  | nil => simpa [field, delimit, scan, splitStep] using tail
  | cons b p ih =>
    cases left <;> simp_all [field, delimit, scan, splitStep]

/-- Concatenation on the canonical representation of a pair of words. -/
theorem polyAppendPair : IsPolyTime (fun p : Bits × Bits => p.1 ++ p.2) := by
  apply polyEncoded (polyField true true)
  rintro ⟨x, y⟩
  change field _ _ (delimit (bitEncode x) ++ bitEncode y) = bitEncode (x ++ y)
  simp [field_delimit, DenseSAT.Converter.bitEncode_list, DenseSAT.Converter.encSnd]

/-- Concatenation of two polynomial-time outputs on a shared input. -/
theorem polyAppend {f g : Bits → Bits} (hf : IsPolyTime f) (hg : IsPolyTime g) :
    IsPolyTime (fun x => f x ++ g x) := (polyPair hf hg).comp polyAppendPair

/-- Adding a self-delimiting bit frame takes polynomial time. -/
theorem polyDelimit : IsPolyTime delimit := by
  let step (_ : Unit) (b : Bool) : Unit × Bits := ((), [true, b])
  have h : scan step (fun _ => [false]) () = delimit := by
    funext x
    induction x with
    | nil => rfl
    | cons b x ih => simp [scan, step, delimit, ih]
  exact h ▸ polyScan step (fun _ => [false]) ()

/-- The tail of the input word is obtained by skipping its first bit. -/
theorem polyTail : IsPolyTime (fun w : Bits => w.tail) := by
  let step (seen b : Bool) : Bool × Bits := (true, if seen then [b] else [])
  have rest (w : Bits) : scan step (fun _ => []) true w = w := by
    induction w with
    | nil => rfl
    | cons b w ih => exact congrArg (b :: ·) ih
  have h : scan step (fun _ => []) false = fun w => w.tail := by
    funext w
    cases w with
    | nil => rfl
    | cons b w => exact rest w
  exact h ▸ polyScan _ _ _

/-- Return the head bit as a one-bit word, defaulting to false at end of input. -/
theorem polyHead : IsPolyTime (fun w : Bits => [w.headD false]) := by
  let step (s : Option Bool) (b : Bool) : Option Bool × Bits := (some (s.getD b), [])
  let fin (s : Option Bool) := [s.getD false]
  have rest (b : Bool) (w : Bits) : scan step fin (some b) w = [b] := by
    induction w with
    | nil => rfl
    | cons a w ih => exact ih
  have h : scan step fin none = fun w => [w.headD false] := by
    funext w
    cases w with
    | nil => rfl
    | cons b w => exact rest b w
  exact h ▸ polyScan _ _ _

/-- A truth table on three computed flag bits is polynomial time. -/
theorem polyBool3 (f : Bool → Bool → Bool → Bool) {a b c : Bits → Bool}
    (ha : IsPolyTime (fun x => [a x])) (hb : IsPolyTime (fun x => [b x]))
    (hc : IsPolyTime (fun x => [c x])) : IsPolyTime (fun x => [f (a x) (b x) (c x)]) := by
  let step (s : Bool × Bool × Bool) (x : Bool) : (Bool × Bool × Bool) × Bits :=
    ((s.2.1, s.2.2, x), [])
  let finish (s : Bool × Bool × Bool) := [f s.1 s.2.1 s.2.2]
  exact (polyAppend ha (polyAppend hb hc)).comp (polyScan step finish (false, false, false))

end Cslib.Complexity.PolynomialEncoding.BitScan
