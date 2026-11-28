/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.Parameterized.CliqueMembership
public import CSLibExt.Computability.Complexity.PolynomialEncoding.Represented
import CSLibExt.Computability.Complexity.PolynomialEncoding.IndexRange
import CSLibExt.Computability.Complexity.PolynomialEncoding.BitZip

/-!
# A machine for the compact Clique circuit

Gate construction traverses an explicit unary count and a table of forbidden
pairs. The references to prior gates are emitted at their binary widths.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.Parameterized.CliqueMembership

open MetaMathlibExt BitstringEncoding ComplexityTheory Cslib.Complexity
open PolynomialEncoding PolynomialEncoding.Comprehension

local notation "Bits" => List Bool
local notation "N" => (bitEncode (α := ℕ))
local notation "E" => (bitEncode (α := ℕ × ℕ))

private theorem encodeMap {α β : Type} [BitstringEncoding β] (xs : List α) (f : α → β) :
    xs.flatMap (fun v => delimit (bitEncode (f v))) = bitEncode (xs.map f) := by
  rw [← frames_encode]
  simp [frames, List.flatMap_map]

private theorem encodeAppend {α : Type} [BitstringEncoding α] (xs ys : List α) :
    bitEncode (xs ++ ys) = bitEncode xs ++ bitEncode ys := by
  simp only [← frames_encode, frames, List.map_append, List.flatMap_append]

private theorem encodePair {α β : Type} [BitstringEncoding α] [BitstringEncoding β]
    (a : α) (b : β) :
    bitEncode (a,b) = pack (bitEncode a) (bitEncode b) := rfl

private theorem encodeSingleton {α : Type} [BitstringEncoding α] (a : α) :
    bitEncode [a] = delimit (bitEncode a) := by
  change delimit (bitEncode a) ++ [] = _
  simp

private theorem encodeDouble {α : Type} [BitstringEncoding α] (a b : α) :
    bitEncode [a,b] = delimit (bitEncode a) ++ delimit (bitEncode b) := by
  change delimit (bitEncode a) ++ bitEncode [b] = _
  rw [encodeSingleton]

/-- The unary count of compact vertices and the encoded forbidden pairs suffice
to generate the entire canonical weighted circuit in polynomial time. -/
theorem represented_exclusionCircuit {D : Type} {e : D → Bits} {m : D → ℕ}
    {ps : D → List (ℕ × ℕ)}
    (hm : Represented e (fun x => unary (m x)))
    (hp : Represented e (fun x => frames E (ps x))) :
    Represented e (fun x => bitEncode (m x, exclusionCircuit (m x) (ps x))) := by
  have number : Represented e (fun x => N (m x)) :=
    (hm.after isPolyTime_encodeLength).transport (by simp)
  have range : Represented e (fun x => frames N (List.range (m x))) :=
    (hm.after IndexRange.isPolyTime_encodeRange).transport (by simp [frames_encode])
  have i : Represented (pair N e) (fun a => N a.1) := (Represented.input N).fst e
  have ig : Represented (pair N e) (fun a => bitEncode ((0, [a.1]) : WCGate)) :=
    ((Represented.const _ (N 0)).packed i.frame).transport
      (by intro p; rw [encodePair, encodeSingleton])
  have inputs := (range.flatMap ig.frame).transport
    (fun x => encodeMap (List.range (m x)) (fun v => ((0, [v]) : WCGate)))
  have left : Represented (pair E e) (fun p => N p.1.1) :=
    ((Represented.input N).fst N).fst e
  have right : Represented (pair E e) (fun p => N p.1.2) :=
    ((Represented.input N).snd N).fst e
  have ag : Represented (pair E e) (fun a => bitEncode ((3, [a.1.1, a.1.2]) : WCGate)) :=
    ((Represented.const _ (N 3)).packed (left.frame.append right.frame)).transport
      (by intro p; rw [encodePair, encodeDouble])
  have ands := (hp.flatMap ag.frame).transport
    (fun x => encodeMap (ps x) (fun p => ((3, [p.1, p.2]) : WCGate)))
  let idx := Represented.numbered E
  have ix : Represented idx (fun p => unary p.2) :=
    ⟨_, BitScan.polyField true false, by intro p; exact hd_pack (unary p.2) (E p.1)⟩
  have off := (((hm.snd idx).append (ix.fst e)).after isPolyTime_encodeLength).transport
    (g := fun p : ((ℕ × ℕ) × ℕ) × D => N (m p.2 + p.1.2))
    (by simp)
  have refs : Represented e (fun x => bitEncode (outputs (m x) (ps x).length)) := by
    apply (hp.enumerate.flatMap off.frame).transport
    intro x
    rw [encodeMap]
    congr 1
    unfold outputs
    have h := List.zipIdx_map_snd 0 (ps x)
    simpa only [List.map_map, Function.comp_def, List.range_eq_range'] using
      congrArg (List.map (m x + ·)) h
  have orGate := (Represented.const e (N 4)).packed refs
  have last := ((hm.append hp.count).after isPolyTime_encodeLength).transport
    (g := fun x => N (m x + (ps x).length)) (by simp)
  have notGate := (Represented.const e (N 2)).packed last.frame
  apply (number.packed (((inputs.append ands).append orGate.frame).append notGate.frame)).transport
  intro x
  rw [encodePair]
  congr 1
  simp only [exclusionCircuit, encodeAppend, encodeDouble, encodePair, encodeSingleton,
    List.append_assoc]

end MetaMathlibExt.Complexity.KeyTheorems.Parameterized.CliqueMembership
