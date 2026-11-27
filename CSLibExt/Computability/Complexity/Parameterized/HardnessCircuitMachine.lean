/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.Parameterized.HardnessNormalFormMachine
public import CSLibExt.Computability.Complexity.PolynomialEncoding.Represented
public import CSLibExt.Computability.Complexity.PolynomialEncoding.BitZip
public import CSLibExt.Computability.Complexity.Parameterized.Identity

/-!
# Certified circuit normalization at a fixed depth

One round computes both polarities of each gate from the preceding round. The
number of rounds is fixed by the depth bound, independently of the input size.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.Parameterized.CircuitNormalMachine

open MetaMathlibExt BitstringEncoding ComplexityTheory Cslib.Complexity.PolynomialEncoding
open Cslib.Complexity.PolynomialEncoding.Comprehension BitScan

local notation "Word" => List Bool

variable {α β : Type} {repr : α → Word}

private theorem bitEncode_nat_inj {i j : ℕ} : bitEncode i = bitEncode j ↔ i = j := by
  constructor
  · intro h
    have eqn := congrArg (bitDecode (α := ℕ)) h
    simpa only [bitDecode_bitEncode, Option.some.injEq] using eqn
  · exact congrArg bitEncode

private theorem reprEqNat {i j : α → ℕ} (hi : Represented repr (fun a => bitEncode (i a)))
    (hj : Represented repr (fun a => bitEncode (j a))) :
    Represented repr (fun a => [decide (i a = j a)]) := by
  apply (Represented.test₂ BitZip.polyEq hi hj).transport
  intro a
  by_cases h : i a = j a
  · simp [h]
  · have hn : Computability.encodeNat (i a) ≠ Computability.encodeNat (j a) :=
      bitEncode_nat_inj.not.mpr h
    simp [h, hn]

private theorem indexed_hit (r : β → Word) (xs : List β) (i s : ℕ) :
    (xs.zipIdx s).flatMap (fun q => if q.2 = s+i then delimit (r q.1) else []) =
      (xs[i]?.map (fun b => delimit (r b))).getD [] := by
  induction xs generalizing i s with
  | nil => simp
  | cons a xs ih =>
    cases i with
    | zero =>
      have skip : (xs.zipIdx (s+1)).flatMap (fun q => if q.2 = s then delimit (r q.1) else []) =
          [] := by
        apply List.flatMap_eq_nil_iff.mpr
        intro q hq
        have := List.le_snd_of_mem_zipIdx hq
        simp [show q.2 ≠ s by omega]
      simp [List.zipIdx_cons, skip]
    | succ i =>
      simp only [List.zipIdx_cons, List.flatMap_cons, List.getElem?_cons_succ]
      simp only [show s + (i+1) = s+1+i by omega, show ¬s = s+1+i by omega, ite_false,
        List.nil_append, ih]

/-- Read a binary-indexed entry of a framed table and use a chosen default when
out of range. Each comparison is between the canonical encodings of the indices. -/
theorem represented_getD (r : β → Word) (d : β) {xs : α → List β} {idx : α → ℕ}
    (rs : Represented repr (fun a => frames r (xs a)))
    (hi : Represented repr (fun a => bitEncode (idx a))) :
    Represented repr (fun a => r ((xs a).getD (idx a) d)) := by
  let marked := Represented.numbered r
  let env := pair marked repr
  have row := (Represented.input marked).fst repr
  have num : Represented env (fun w => bitEncode w.1.2) := by
    apply ((row.after (polyField true false)).after isPolyTime_encodeLength).transport
    intro w
    simp [marked, Represented.numbered, field_delimit, pack, unary]
  have val : Represented env (fun w => r w.1.1) := by
    apply (row.after (polyField false true)).transport
    intro w
    simp [marked, Represented.numbered, field_delimit, pack]
  have eqn := reprEqNat num (hi.snd marked)
  have hit := rs.enumerate.flatMap (eqn.cond val.frame (Represented.const _ []))
  let scanned (a : α) := ((xs a)[idx a]?.map (fun b => delimit (r b))).getD []
  have encoded : Represented repr scanned := by
    apply hit.transport
    intro a
    simpa only [scanned, Nat.zero_add, decide_eq_true_eq] using indexed_hit r (xs a) (idx a) 0
  apply ((encoded.after polyEmpty).cond (Represented.const repr (r d))
    (encoded.after (polyField true false))).transport
  intro a
  rw [List.getD_eq_getElem?_getD]
  cases h : (xs a)[idx a]? with
  | none => simp [scanned, h]
  | some b =>
    have hn : (delimit (r b)).isEmpty = false := by cases r b <;> rfl
    have hl := field_delimit true false (r b) []
    simp only [List.append_nil, ite_true, Bool.false_eq_true, ite_false] at hl
    simp [scanned, h, hn, hl]

/-- A signed literal carries its binary variable index and one polarity bit. -/
def literal (v : ℕ × Bool) : Word := pack (bitEncode v.1) [v.2]

/-- A typed family of alternatives with indexed, signed literals. -/
abbrev Family := NormalFormMachine.FamilyOf (ℕ × Bool)

/-- The machine word representing the typed formula family. -/
def familyWord (ps : Family) :=
  NormalFormMachine.encodeFamily (NormalFormMachine.mapFamily literal ps)

/-- Positive and negative normal forms for the same gate. -/
abbrev Node := Family × Family

/-- Both polarities are written to the table, with the positive form first. -/
def nodeWord := pair familyWord familyWord

/-- A constant Boolean constraint as a singleton family. -/
def constant (b p : Bool) : Family := if b = p then [[]] else [[[]]]

/-- The default for a reference beyond the available gate table. -/
def falseNode : Node := (constant false true, constant false false)

/-- Select the requested output polarity. -/
def atPolarity (p : Bool) (x : Node) := if p then x.1 else x.2

/-- Normalize one polarity of a gate against an already computed table. -/
def gate (n : ℕ) (prev : List Node) (g : WCGate) (pos : Bool) : Family :=
  let k := g.1
  let rs := g.2
  let i := rs.headD 0
  let read (j : ℕ) (p : Bool) := atPolarity p (prev.getD j falseNode)
  if k = 3 then NormalFormMachine.combineFamilies pos (rs.map (read · pos))
  else if k = 4 then NormalFormMachine.combineFamilies (!pos) (rs.map (read · pos))
  else if rs.length = 1 then
    if k = 0 then if i < n then [[[(i,pos)]]] else constant false pos
    else if k = 1 then constant (i = 1) pos
    else if k = 2 then read i (!pos)
    else constant false pos
  else constant false pos

/-- Synchronous normalization with boundedly many rounds. -/
def table (n : ℕ) (C : List WCGate) : ℕ → List Node
  | 0 => []
  | d+1 =>
    let prev := table n C d
    C.map fun g => (gate n prev g true, gate n prev g false)

private theorem reprLT {i j : α → ℕ} (hi : Represented repr (fun a => bitEncode (i a)))
    (hj : Represented repr (fun a => bitEncode (j a))) :
    Represented repr (fun a => [decide (i a < j a)]) := by
  apply (hj.test₂ BitZip.polyDecodedLE hi).neg.transport
  intro a
  change [!decide (Computability.decodeNat (Computability.encodeNat _) ≤
    Computability.decodeNat (Computability.encodeNat _))] = _
  by_cases h : i a < j a
  · simp [Computability.decode_encodeNat, h, Nat.not_le_of_gt h]
  · simp [Computability.decode_encodeNat, h, Nat.le_of_not_gt h]

private theorem reprSide {a : α → Node} (p : Bool)
    (ha : Represented repr (fun x => nodeWord (a x))) :
    Represented repr (fun x => familyWord (atPolarity p (a x))) := by
  cases p
  · apply (ha.after (polyField false true)).transport
    intro x
    exact tl_pack _ _
  · apply (ha.after (polyField true false)).transport
    intro x
    exact hd_pack _ _

private theorem reprCombine (p : Bool) {a : α → List Family}
    (ha : Represented repr (fun x => frames familyWord (a x))) :
    Represented repr (fun x => familyWord (NormalFormMachine.combineFamilies p (a x))) := by
  apply (ha.after (NormalFormMachine.polyCombine p)).transport
  intro x
  exact NormalFormMachine.combine_encoded literal _ _

/-- Normalize one gate given a represented table of preceding-round results. -/
theorem represented_gate {n : α → ℕ} {prev : α → List Node} {g : α → WCGate}
    (hn : Represented repr (fun x => bitEncode (n x)))
    (hp : Represented repr (fun x => frames nodeWord (prev x)))
    (hg : Represented repr (fun x => bitEncode (g x))) (pos : Bool) :
    Represented repr (fun x => familyWord (gate (n x) (prev x) (g x) pos)) := by
  let N := bitEncode (α := ℕ)
  let kind (x : α) := (g x).1
  let refs (x : α) := (g x).2
  let first (x : α) := (refs x).headD 0
  have hk : Represented repr (fun x => N (kind x)) :=
    (hg.after (polyField true false)).transport (fun x => hd_pack _ _)
  have hr : Represented repr (fun x => frames N (refs x)) :=
    (hg.after (polyField false true)).transport
      (fun x => (tl_pack _ _).trans (frames_encode _).symm)
  have hfirst : Represented repr (fun x => N (first x)) := by
    apply (hr.after (polyField true false)).transport
    intro x
    cases h : refs x with
    | nil => simp [first, h, frames, N]; rfl
    | cons i rs =>
      change hd (pack (N i) (frames N rs)) = N (first x)
      simp [first, h]
  have hlen : Represented repr (fun x => N (refs x).length) :=
    (hr.count.after isPolyTime_encodeLength).transport (by simp [N])
  have cn (c : ℕ) : Represented repr (fun _ => N c) := Represented.const _ _
  have isKind (c : ℕ) := reprEqNat hk (cn c)
  have no : Represented repr (fun _ => familyWord (constant false pos)) := Represented.const _ _
  have yes : Represented repr (fun _ => familyWord (constant true pos)) := Represented.const _ _
  have var : Represented repr (fun x => familyWord [[[(first x, pos)]]]) := by
    have h := (hfirst.packed (Represented.const repr [pos])).frame.frame.frame
    apply h.transport
    intro x
    simp [familyWord, NormalFormMachine.encodeFamily, NormalFormMachine.encodeFormula,
      NormalFormMachine.mapFamily, NormalFormMachine.frames, literal, N]
  have inRange := reprLT hfirst hn
  have hconst := (reprEqNat hfirst (cn 1)).cond yes no
  have arg := reprSide (!pos) (represented_getD nodeWord falseNode hp hfirst)
  have allArgs : Represented repr (fun x => frames familyWord ((refs x).map fun j =>
      atPolarity pos ((prev x).getD j falseNode))) := by
    exact hr.mapped (reprSide pos (represented_getD nodeWord falseNode (hp.snd N)
      ((Represented.input N).fst repr)))
  have both := (isKind 3).cond (reprCombine pos allArgs)
    ((isKind 4).cond (reprCombine (!pos) allArgs)
      ((reprEqNat hlen (cn 1)).cond ((isKind 0).cond (inRange.cond var no)
        ((isKind 1).cond hconst ((isKind 2).cond arg no))) no))
  apply both.transport
  intro x
  simp only [decide_eq_true_eq, gate, kind, refs, first]
  split_ifs <;> simp_all

/-- For each fixed round bound, a TM2 evaluator writes both polarities of every gate. -/
theorem represented_table {n : α → ℕ} {C : α → List WCGate}
    (hn : Represented repr (fun x => bitEncode (n x)))
    (hc : Represented repr (fun x => frames bitEncode (C x))) (d : ℕ) :
    Represented repr (fun x => frames nodeWord (table (n x) (C x) d)) := by
  induction d with
  | zero => exact Represented.const repr []
  | succ d ih =>
    let G := bitEncode (α := WCGate)
    have gateInput := (Represented.input G).fst repr
    have h (p : Bool) := represented_gate (hn.snd G) (ih.snd G) gateInput p
    exact hc.mapped (t := nodeWord) (body := fun p =>
      (gate (n p.2) (table (n p.2) (C p.2) d) p.1 true,
        gate (n p.2) (table (n p.2) (C p.2) d) p.1 false)) ((h true).packed (h false))

end MetaMathlibExt.Complexity.KeyTheorems.Parameterized.CircuitNormalMachine
