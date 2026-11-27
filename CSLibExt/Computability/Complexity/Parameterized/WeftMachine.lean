/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.Parameterized.Weft
public import CSLibExt.Computability.Complexity.Parameterized.Identity
import CSLibExt.Computability.Complexity.PolynomialEncoding.IndexRange
public import CSLibExt.Computability.Complexity.PolynomialEncoding.BitOperations
import CSLibExt.Computability.Complexity.PolynomialEncoding.ListParts

/-!
# Machine realization of the W-hierarchy inclusion

The machine copies its input and scans its outer frames. For a complete
header and at least one gate it appends a probe and a relay. Gate payloads
can be copied verbatim, including noncanonical representations.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.Parameterized

open BitstringEncoding ComplexityTheory
open Cslib.Complexity.PolynomialEncoding
open Cslib.Complexity.PolynomialEncoding.BitScan

local notation "Bits" => List Bool

-- The first coordinate distinguishes a frame boundary, a tag inside a
-- frame, and a pending data bit. The second saturates the frame count at two.
namespace WeftMachine

abbrev ScanState := Option Bool × Option Bool

def bump : Option Bool → Option Bool
  | none => some false
  | some _ => some true

def frameStep (count : Bool) (s : ScanState) (b : Bool) : ScanState × Bits :=
  if s.1 == some true then ((some false, s.2), [])
  else if b then ((some true, s.2), [])
  else ((none, bump s.2), if count && s.2.isSome then [true] else [])

def frameEnd (s : ScanState) : Bits :=
  [s.1.isNone && s.2 == some true]

def frameFlag := scan (frameStep false) frameEnd (none, none)

def gateCount := scan (frameStep true) (fun _ => []) (none, none)

private def between (inner : Bool) : Option Bool := if inner then some false else none

private theorem scan_delimit (count : Bool) (finish : ScanState → Bits) (seen : Option Bool)
    (p r : Bits) (inner : Bool) :
    scan (frameStep count) finish (between inner, seen) (delimit p ++ r) =
      (if count && seen.isSome then [true] else []) ++
        scan (frameStep count) finish (none, bump seen) r := by
  induction p generalizing inner with
  | nil => cases inner <;> rfl
  | cons b p ih =>
    cases inner <;> exact ih true

private def frames (ps : List Bits) : Bits := (ps.map delimit).flatten

private theorem scan_frames (count : Bool) (finish : ScanState → Bits)
    (ps : List Bits) (r : Bits) :
    scan (frameStep count) finish (none, some true) (frames ps ++ r) =
      (if count then List.replicate ps.length true else []) ++
        scan (frameStep count) finish (none, some true) r := by
  induction ps with
  | nil => simp [frames]
  | cons p ps ih =>
    change scan _ _ (between false, some true) ((delimit p ++ frames ps) ++ r) = _
    rw [List.append_assoc, scan_delimit]
    change (if count && true then [true] else []) ++
      scan _ _ (none, some true) (frames ps ++ r) = _
    rw [ih]
    cases count <;> simp [List.replicate_succ]

private theorem flag_frames (p q : Bits) (ps : List Bits) :
    frameFlag (delimit p ++ delimit q ++ frames ps) = [true] := by
  change scan _ _ (between false, none) _ = _
  rw [List.append_assoc, scan_delimit]
  change scan _ _ (between false, some false) _ = _
  rw [scan_delimit]
  change scan _ _ (none, some true) (frames ps) = _
  simpa [scan, frameEnd] using scan_frames false frameEnd ps []

private theorem count_frames (p q : Bits) (ps : List Bits) :
    (gateCount (delimit p ++ delimit q ++ frames ps)).length = ps.length + 1 := by
  change (scan _ _ (between false, none) _).length = _
  rw [List.append_assoc, scan_delimit]
  change (scan _ _ (between false, some false) _).length = _
  rw [scan_delimit]
  have h := scan_frames true (fun _ => []) ps []
  simpa [scan, bump] using congrArg (fun w : Bits => (true :: w).length) h

private theorem flag_incomplete (r : Bits) (h : undelimit r = none) (inner : Bool)
    (hn : r ≠ [] ∨ inner = true) (seen : Option Bool) :
    scan (frameStep false) frameEnd (between inner, seen) r = [false] := by
  match r with
  | [] => have : inner = true := hn.resolve_left (by simp); subst inner; rfl
  | false :: rs => simp [undelimit] at h
  | [true] => cases inner <;> rfl
  | true :: b :: rs =>
    have hh : undelimit rs = none := by
      cases hu : undelimit rs <;> simp_all [undelimit]
    have ht := flag_incomplete rs hh true (Or.inr rfl) seen
    cases inner <;> exact ht
termination_by r.length

private theorem decompose_frames (x : Bits) :
    ∃ (ps : List Bits) (r : Bits), x = frames ps ++ r ∧ undelimit r = none := by
  cases h : undelimit x with
  | none => exact ⟨[], x, rfl, h⟩
  | some pr =>
    obtain ⟨p,r⟩ := pr
    have hx := (Cslib.CookLevin.undelimit_eq_some_iff _ _ _).mp h
    have hr : r.length < x.length := by rw [hx, List.length_append, length_delimit]; omega
    obtain ⟨ps,s,hr',hs⟩ := decompose_frames r
    refine ⟨p :: ps,s,?_,hs⟩
    simp only [frames, List.map_cons, List.flatten_cons, List.append_assoc]
    exact hx.trans (congrArg (delimit p ++ ·) hr')
termination_by x.length

private theorem flag_frames_incomplete (ps : List Bits) (r : Bits) (hn : r ≠ [])
    (h : undelimit r = none) :
    frameFlag (frames ps ++ r) = [false] := by
  cases ps with
  | nil => exact flag_incomplete r h false (Or.inl hn) none
  | cons p ps =>
    change scan _ _ (between false, none) ((delimit p ++ frames ps) ++ r) = _
    rw [List.append_assoc, scan_delimit]
    cases ps with
    | nil => exact flag_incomplete r h false (Or.inl hn) (some false)
    | cons q ps =>
      change scan _ _ (between false, some false) ((delimit q ++ frames ps) ++ r) = _
      rw [List.append_assoc, scan_delimit]
      change scan _ _ (none, some true) (frames ps ++ r) = _
      rw [scan_frames]
      exact flag_incomplete r h false (Or.inl hn) (some true)

private def constStep (_ : Unit) (_ : Bool) : Unit × Bits := ((), [])

private theorem polyConst (c : Bits) : IsPolyTime (fun _ : Bits => c) := by
  have h : scan constStep (fun _ => c) () = fun _ => c := by
    funext w
    induction w with
    | nil => rfl
    | cons b w ih => exact ih
  exact h ▸ polyScan constStep (fun _ => c) ()

private theorem polyId : IsPolyTime (fun x : Bits => x) := by
  let step (_ : Unit) (b : Bool) : Unit × Bits := ((), [b])
  have h : scan step (fun _ => []) () = fun x => x := by
    funext w
    induction w with
    | nil => rfl
    | cons b w ih => exact congrArg (b :: ·) ih
  exact h ▸ polyScan step (fun _ => []) ()

def keepStep : Option Bool → Bool → Option Bool × Bits
  | none, b => (some b, [])
  | some keep, b => (some keep, if keep then [b] else [])

def keepIf := scan keepStep (fun _ => []) none

private theorem keepIf_cons (b : Bool) (x : Bits) :
    keepIf (b :: x) = if b then x else [] := by
  change scan _ _ (some b) x = _
  induction x with
  | nil => cases b <;> rfl
  | cons a x ih => cases b <;> simp_all [scan, keepStep]

def extraGates (m : ℕ) : List WCGate := [(3, probeRefs m), (4, [m-1])]

private theorem encode_list_append {α : Type} [BitstringEncoding α] (a b : List α) :
    bitEncode (a ++ b) = bitEncode a ++ bitEncode b := by
  change (((a ++ b).map bitEncode).map delimit).flatten = _
  simp only [List.map_append, List.flatten_append]
  rfl

private theorem encode_extra (m : ℕ) :
    bitEncode (extraGates m) =
    delimit (delimit (bitEncode (3 : ℕ)) ++
      (bitEncode (List.range m) ++ bitEncode ([0,0,0] : List ℕ))) ++
    delimit (delimit (bitEncode (4 : ℕ)) ++ delimit (bitEncode (m-1))) := by
  change delimit (delimit (bitEncode (3 : ℕ)) ++ bitEncode (probeRefs m)) ++
      (delimit (delimit (bitEncode (4 : ℕ)) ++ (delimit (bitEncode (m-1)) ++ [])) ++ []) = _
  simp [probeRefs, encode_list_append]

private theorem polyExtra : IsPolyTime (fun w : Bits => bitEncode (extraGates w.length)) := by
  let hRange := IndexRange.isPolyTime_encodeRange
  have h₁ := (polyAppend (polyConst (delimit (bitEncode (3 : ℕ))))
    (polyAppend hRange (polyConst (bitEncode ([0,0,0] : List ℕ))))).comp polyDelimit
  have h₂ := (polyAppend (polyConst (delimit (bitEncode (4 : ℕ))))
    ((polyTail.comp isPolyTime_encodeLength).comp polyDelimit)).comp polyDelimit
  have h := polyAppend h₁ h₂
  simpa only [encode_extra, List.length_tail, Function.comp_def] using h

end WeftMachine

open WeftMachine

/-- Copy the raw input and append the two extra gates when its outer framing
contains a header and at least one complete gate. -/
def promoteWeftWord (x : Bits) : Bits :=
  x ++ keepIf (frameFlag x ++ bitEncode (extraGates (gateCount x).length))

/-- The W-hierarchy promotion is computed by polynomial-time TM2 machines
on the canonical input and output representations. -/
theorem isPolyTime_promoteWeftWord : IsPolyTime promoteWeftWord :=
  polyAppend polyId ((polyAppend (polyScan (frameStep false) frameEnd (none, none))
    ((polyScan (frameStep true) (fun _ => []) (none, none)).comp polyExtra)).comp
    (polyScan keepStep (fun _ => []) none))

private theorem promoted_decode (x : Bits) :
    bitDecode (α := ℕ × List WCGate) (promoteWeft x) =
      (bitDecode (α := ℕ × List WCGate) x).map (fun q => (q.1, promoteWeftCircuit q.2)) := by
  cases h : bitDecode (α := ℕ × List WCGate) x with
  | none =>
    rw [show promoteWeft x = [] by simp [promoteWeft, h]]
    rfl
  | some q => simp [promoteWeft, h]

private theorem decode_product {α β : Type} [BitstringEncoding α] [BitstringEncoding β]
    (x : Bits) : bitDecode (α := α × β) x =
      (match undelimit x with
        | none => none | some (p, r) =>
          match bitDecode (α := α) p, bitDecode (α := β) r with
          | some a, some b => some (a, b) | _, _ => none) := rfl

private theorem decode_frame {α β : Type} [BitstringEncoding α] [BitstringEncoding β]
    (p r : Bits) : bitDecode (α := α × β) (delimit p ++ r) =
      (match bitDecode (α := α) p, bitDecode (α := β) r with
       | some a, some b => some (a, b) | _, _ => none) := by
  rw [decode_product, undelimit_delimit]

private theorem decode_header (p r : Bits) :
    bitDecode (α := ℕ × List WCGate) (delimit p ++ r) =
      (bitDecode (α := List WCGate) r).map (fun C => (Computability.decodeNat p, C)) := by
  rw [decode_frame, show bitDecode (α := ℕ) p = some (Computability.decodeNat p) by rfl]
  cases bitDecode (α := List WCGate) r <;> rfl

private theorem decode_gates_append (ps : List Bits) (gates : List WCGate) :
    bitDecode (α := List WCGate) (frames ps ++ bitEncode gates) =
      (bitDecode (α := List WCGate) (frames ps)).map (· ++ gates) := by
  induction ps with
  | nil => exact bitDecode_bitEncode gates
  | cons p ps ih =>
    change bitDecode ((delimit p ++ frames ps) ++ bitEncode gates) =
      (bitDecode (α := List WCGate) (delimit p ++ frames ps)).map _
    rw [List.append_assoc, decode_list_delimit, decode_list_delimit, ih]
    cases bitDecode (α := WCGate) p <;>
      cases bitDecode (α := List WCGate) (frames ps) <;> rfl

private theorem length_decode_frames (ps : List Bits) {C : List WCGate}
    (h : bitDecode (frames ps) = some C) : C.length = ps.length := by
  induction ps generalizing C with
  | nil => have e : some ([] : List WCGate) = some C := h; cases e; rfl
  | cons p ps ih =>
    change bitDecode (delimit p ++ frames ps) = some C at h
    rw [decode_list_delimit] at h
    obtain ⟨g, _, hg⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨gs, hgs, rfl⟩ := Option.map_eq_some_iff.mp hg
    simp [ih hgs]

private theorem decode_gates_incomplete (ps : List Bits) {r : Bits}
    (hn : r ≠ []) (h : undelimit r = none) :
    bitDecode (α := List WCGate) (frames ps ++ r) = none := by
  induction ps with
  | nil => exact decode_list_none_of_undelimit_none hn h
  | cons p ps ih =>
    change bitDecode (α := List WCGate) ((delimit p ++ frames ps) ++ r) = _
    rw [List.append_assoc, decode_list_delimit, ih]
    cases bitDecode (α := WCGate) p <;> rfl

/-- The byte-preserving machine and the normalized circuit construction
decode identically on every bitstring. -/
theorem decode_promoteWeftWord (x : Bits) :
    bitDecode (α := ℕ × List WCGate) (promoteWeftWord x) = bitDecode (promoteWeft x) := by
  rw [promoted_decode]
  obtain ⟨ps,r,rfl,hparse⟩ := decompose_frames x
  by_cases he : r = []
  · subst r
    simp only [List.append_nil]
    cases ps with
    | nil => rfl
    | cons p ps =>
      cases ps with
      | nil =>
        have h : frameFlag (frames [p]) = [false] := by
          change scan _ _ (between false, none) (delimit p ++ []) = _
          rw [scan_delimit]
          rfl
        simp only [promoteWeftWord, h, List.singleton_append, keepIf_cons, Bool.false_eq_true,
          ite_false, List.append_nil]
        change bitDecode (delimit p ++ []) = (bitDecode (delimit p ++ [])).map _
        rw [decode_header]
        rfl
      | cons q ps =>
        let w := delimit p ++ delimit q ++ frames ps
        have hw : frames (p :: q :: ps) = w := List.append_assoc .. |>.symm
        rw [hw]
        have flag : frameFlag w = [true] := flag_frames p q ps
        have count : (gateCount w).length = (q :: ps).length := count_frames p q ps
        simp only [promoteWeftWord, flag, count, List.singleton_append, keepIf_cons, ite_true]
        have hw' : w = delimit p ++ frames (q :: ps) := hw.symm
        rw [hw', List.append_assoc]
        rw [decode_header, decode_header, decode_gates_append]
        cases h : bitDecode (α := List WCGate) (frames (q :: ps)) with
        | none => rfl
        | some C =>
          have hlen := length_decode_frames _ h
          have hne : C ≠ [] := fun e => by rw [e] at hlen; simp at hlen
          simp [promoteWeftCircuit, extraGates, hlen, hne]
  · have flag := flag_frames_incomplete ps r he hparse
    simp only [promoteWeftWord, flag, List.singleton_append, keepIf_cons,
      Bool.false_eq_true, ite_false, List.append_nil]
    have h : bitDecode (α := ℕ × List WCGate) (frames ps ++ r) = none := by
      cases ps with
      | nil =>
        change bitDecode (α := ℕ × List WCGate) r = none
        rw [decode_product, hparse]
      | cons p ps =>
        change bitDecode ((delimit p ++ frames ps) ++ r) = _
        rw [List.append_assoc, decode_header, decode_gates_incomplete ps he hparse]
        rfl
    rw [h]
    rfl

/-- A parameter-preserving polynomial-time circuit augmentation takes every
member of W[t] into W[t+1], raising the depth bound by one. -/
theorem wLevel_subset_succ (t : ℕ) : WLevel t ⊆ WLevel (t + 1) := by
  rintro P ⟨d,h⟩
  refine ⟨d+1, h.postcomp_instance isPolyTime_promoteWeftWord ?_⟩
  intro x k
  rw [weightedCircuitSat_congr_decode (decode_promoteWeftWord x),
    weightedCircuitSat_promoteWeft]

end MetaMathlibExt.Complexity.KeyTheorems.Parameterized
