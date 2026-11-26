/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Defs
import CSLibExt.Computability.Complexity.BoolClosure
import CSLibExt.Computability.Complexity.Preimage
import Mathlib.Tactic.FinCases

/-!
# Polynomial-time streaming on bit strings

Finite-state scans compute bit-string output using bounded chunks. They can copy or transform
framed payloads, emit a fixed word per frame, and test whether framing is complete. The closure
lemmas combine these passes without opening up their machine implementations.
-/

public section

namespace Cslib.Complexity.PolynomialEncoding.StreamScan

open MetaMathlibExt ComplexityTheory BitstringEncoding Turing Function TM2Program
open Cslib.Complexity

/-- Scan a raw bit string with initial state `q`, concatenating the output of each transition
and the final output specified by `finish`. -/
@[expose] def scan {Q : Type} (step : Q → Bool → Q × List Bool) (finish : Q → List Bool)
    (q : Q) : List Bool → List Bool
  | [] => finish q
  | b :: x => (step q b).2 ++ scan step finish (step q b).1 x

/-- If the state type `Q` is finite, `scan step finish q₀` is polynomial-time in the input length.
The machine stores output in reverse order and reverses it once at the end. Each transition emits
a bounded number of bits because the state and input alphabets are finite. -/
theorem polyScan {Q : Type} [Finite Q]
    (step : Q → Bool → Q × List Bool) (finish : Q → List Bool) (q₀ : Q) :
    IsPolyTime (scan step finish q₀) := by
  classical
  let := Fintype.ofFinite Q
  let prog : Q ⊕ Bool → TM2.Stmt (fun _ : Fin 3 => Bool) (Q ⊕ Bool) Bool
    | .inl q =>
      .peek 0 (fun _ o => o.isNone) <| .branch id
        (emit 1 (finish q) (.inr false))
        (.pop 0 (fun _ o => o.getD false) <| .branch id
          (emit 1 (step q true).2 (.inl (step q true).1))
          (emit 1 (step q false).2 (.inl (step q false).1)))
    | .inr false => moveB 1 2 some id (.inr false) (.inr true)
    | .inr true => .halt
  let comp : Host.Comp := {
    K := Fin 3, Γ := fun _ => Bool, L := Q ⊕ Bool, prog := prog,
    ks := [0, 1, 2], ks_nodup := by decide, mem_ks := by decide }
  let st (x r o : List Bool) : Fin 3 → List Bool
    | 0 => x
    | 1 => r
    | _ => o
  have up0 (x r o l : List Bool) : update (st x r o) 0 l = st l r o := by
    funext k
    fin_cases k <;> rfl
  have up1 (x r o l : List Bool) : update (st x r o) 1 l = st x l o := by
    funext k
    fin_cases k <;> rfl
  have hr (x : List Bool) (q : Q) (v : Bool) (r : List Bool) :
      Run prog (x.length + 1) ⟨some (.inl q), v, st x r []⟩
        ⟨some (.inr false), true, st [] ((scan step finish q x).reverse ++ r) []⟩ := by
    induction x generalizing q v r with
    | nil =>
      apply Run.single
      simp [prog, TM2.stepAux, emit, stepAux_pushList, scan, up1, st]
    | cons b x ih =>
      have h := ih (step q b).1 b ((step q b).2.reverse ++ r)
      simp only [scan, List.reverse_append, List.append_assoc]
      refine Run.head ?_ h
      cases b <;>
        simp [TM2.step, prog, TM2.stepAux, emit, stepAux_pushList, up0, up1, st]
  let B := Finset.univ.sup fun q : Q =>
    max (finish q).length (max (step q true).2.length (step q false).2.length)
  have bound (x : List Bool) (q : Q) : (scan step finish q x).length ≤ (x.length + 1) * B := by
    have h (q : Q) : max (finish q).length
        (max (step q true).2.length (step q false).2.length) ≤ B :=
      Finset.le_sup (f := fun q : Q =>
        max (finish q).length (max (step q true).2.length (step q false).2.length))
        (Finset.mem_univ q)
    induction x generalizing q with
    | nil => simpa [scan] using (le_max_left _ _).trans (h q)
    | cons b x ih =>
      have hb : (step q b).2.length ≤ B := by cases b <;> have := h q <;> omega
      have hi := ih (step q b).1
      simp only [scan, List.length_append, List.length_cons, Nat.succ_mul] at hi ⊢
      omega
  apply Host.isPolyTime_reduction (c := comp) (cX := 0) (cO := 2)
    (gX := id) (start := .inl q₀) (done := .inr true) (Equiv.refl Bool) _
    ((Polynomial.X + 1) * (Polynomial.C B + 1) + 1) rfl
  intro x
  let y := scan step finish q₀ x
  have h₁ := hr x q₀ false []
  simp only [List.append_nil] at h₁
  obtain ⟨v, S, h₂, _, ho, _⟩ := moveB_run (M := prog)
    (self := Sum.inr false) (next := .inr true) (a := (1 : Fin 3)) (b := 2)
    (d := some) (g := id) rfl (by decide) y.reverse y.reverse [] true
    (st [] y.reverse []) (by simp [st]) rfl rfl
  have hi : update (fun _ : Fin 3 => ([] : List Bool)) 0 x = st x [] [] := by
    funext k
    fin_cases k <;> rfl
  refine ⟨v, S, ?_, ?_⟩
  · change RunLe prog _ ⟨_, _, update _ 0 (x.map id)⟩ _
    rw [List.map_id, hi]
    apply (h₁.trans h₂).le
    have := bound x q₀
    simp [y, Nat.mul_add] at *
    omega
  · simpa [y, st, comp] using ho

private theorem polyPair {f g : List Bool → List Bool} (hf : IsPolyTime f) (hg : IsPolyTime g) :
    IsPolyTime (fun x => (f x, g x)) :=
  ((isPolyTime_dup.comp hg.map_fst).comp isPolyTime_swap).comp hf.map_fst

/-- Transfer a raw-string computation to encoded inputs and outputs. -/
private theorem polyEncoded {α β : Type} [BitstringEncoding α] [BitstringEncoding β]
    {f : List Bool → List Bool} (hf : IsPolyTime f) {g : α → β}
    (he : ∀ a, f (bitEncode a) = bitEncode (g a)) : IsPolyTime g := by
  obtain ⟨m⟩ := Preimage.raw_computable hf
  refine ⟨{ m with outputsFun := fun a => ?_ }⟩
  have h := m.outputsFun (bitEncode a)
  simp only [he] at h
  exact h

/-- Read the first delimited field, then copy the suffix. Each output can be enabled separately. -/
private def splitStep (left right : Bool) : Option Bool → Bool → Option Bool × List Bool
  | none, b => (none, if right then [b] else [])
  | some false, b => (if b then some true else none, [])
  | some true, b => (some false, if left then [b] else [])

/-- Extract the payload of the first frame, the suffix after it, or both, as selected by
`left` and `right`. -/
def field (left right : Bool) := scan (splitStep left right) (fun _ => []) (some false)

/-- Extracting fields from a raw bit string takes polynomial time. -/
theorem polyField (left right : Bool) : IsPolyTime (field left right) :=
  polyScan _ _ _

/-- On a complete first frame, the selected payload and suffix are copied without framing. -/
theorem field_delimit (left right : Bool) (p r : List Bool) :
    field left right (delimit p ++ r) = (if left then p else []) ++ (if right then r else []) := by
  have tail : scan (splitStep left right) (fun _ => []) none r = if right then r else [] := by
    induction r with
    | nil => cases right <;> rfl
    | cons b r ih => cases right <;> simp_all [scan, splitStep]
  induction p with
  | nil => simpa [field, delimit, scan, splitStep] using tail
  | cons b p ih =>
    cases left <;> simp_all [field, delimit, scan, splitStep]

/-- Two polynomial-time bit-string maps on the same input can have their outputs concatenated
in polynomial time. -/
theorem polyAppend {f g : List Bool → List Bool} (hf : IsPolyTime f) (hg : IsPolyTime g) :
    IsPolyTime (fun x => f x ++ g x) := by
  apply (polyPair hf hg).comp (g := fun p : List Bool × List Bool => p.1 ++ p.2)
  apply polyEncoded (polyField true true)
  rintro ⟨x, y⟩
  change field _ _ (delimit (bitEncode x) ++ bitEncode y) = bitEncode (x ++ y)
  simp [field_delimit, DenseSAT.Converter.bitEncode_list, DenseSAT.Converter.encSnd]

/-- Delimiting a raw bit string takes polynomial time. -/
theorem polyDelimit : IsPolyTime delimit := by
  let step (_ : Unit) (b : Bool) : Unit × List Bool := ((), [true, b])
  have h : scan step (fun _ => [false]) () = delimit := by
    funext x
    induction x with
    | nil => rfl
    | cons b x ih => simp [scan, step, delimit, ih]
  exact h ▸ polyScan step (fun _ => [false]) ()

/-! ### Streaming over delimited frames -/

-- The first state component is true when a payload bit is due. The second is the last payload
-- bit of this frame, or `none` before the first payload bit.
private def blockStep (initial : List Bool) (bit : Bool → List Bool)
    (close : Option Bool → List Bool) (q : Bool × Option Bool) (b : Bool) :
    (Bool × Option Bool) × List Bool :=
  if q.1 then ((false, some b), bit b)
  else
    let start := if q.2.isNone then initial else []
    if b then ((true, q.2), start) else ((false, none), start ++ close q.2)

/-- Transform a raw sequence of frames: emit `initial` when a frame starts, apply `bit` to each
payload bit, and apply `close` to the last payload bit (or `none` for an empty payload) at its
terminator. An incomplete trailing frame has no closing output. -/
def blocks (initial : List Bool) (bit : Bool → List Bool) (close : Option Bool → List Bool) :
    List Bool → List Bool :=
  scan (blockStep initial bit close) (fun _ => []) (false, none)

/-- A framed scan on empty input emits nothing. -/
@[simp] theorem blocks_nil (initial : List Bool) (bit : Bool → List Bool)
    (close : Option Bool → List Bool) : blocks initial bit close [] = [] := by
  simp [blocks, scan]

/-- Transforming framed input with fixed output chunks takes polynomial time. -/
theorem polyBlocks (initial : List Bool) (bit : Bool → List Bool)
    (close : Option Bool → List Bool) :
    IsPolyTime (blocks initial bit close) :=
  polyScan _ _ _

/-- A complete frame emits its initial, the transformed payload, and the closing chunk; the scan
resumes on the suffix in its initial state. -/
theorem blocks_frame (initial : List Bool) (bit : Bool → List Bool)
    (close : Option Bool → List Bool) (p r : List Bool) :
    blocks initial bit close (delimit p ++ r) =
      initial ++ p.flatMap bit ++ close p.getLast? ++ blocks initial bit close r := by
  have inside (xs : List Bool) (last : Bool) :
      scan (blockStep initial bit close) (fun _ => []) (false, some last) (delimit xs ++ r) =
        xs.flatMap bit ++ close (xs.getLast?.orElse fun _ => some last) ++
          blocks initial bit close r := by
    induction xs generalizing last with
    | nil => simp [scan, delimit, blocks, blockStep]
    | cons b xs ih =>
      simp only [delimit, List.cons_append, scan, blockStep, Bool.false_eq_true, ↓reduceIte,
        Option.isNone_some, List.nil_append, List.flatMap_cons, List.append_assoc, ih]
      cases xs with
      | nil => rfl
      | cons c cs =>
        obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp
          (show (c :: cs).getLast?.isSome by simp)
        simp [hd]
  cases p with
  | nil => simp [blocks, scan, blockStep, delimit, List.append_assoc]
  | cons b p =>
    simp only [blocks, delimit, List.cons_append, scan, blockStep, Bool.false_eq_true,
      ↓reduceIte, Option.isNone_none, List.flatMap_cons, List.append_assoc, inside]
    cases p with
    | nil => rfl
    | cons c cs =>
      obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp
        (show (c :: cs).getLast?.isSome by simp)
      simp [hd]

/-- Emit `mark` once per complete frame, ignoring every payload. -/
@[expose] def marks (mark : List Bool) : List Bool → List Bool :=
  blocks [] (fun _ => []) (fun _ => mark)

/-- On a fully framed list, marking gives one copy of `mark` per payload. -/
theorem marks_frames (ps : List (List Bool)) (mark : List Bool) :
    marks mark (ps.map delimit).flatten = (List.replicate ps.length mark).flatten := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    have he : p.flatMap (fun _ => ([] : List Bool)) = [] := by induction p <;> simp_all
    simp only [List.map_cons, List.flatten_cons, List.length_cons, List.replicate_succ]
    unfold marks at ih ⊢
    rw [blocks_frame, he]
    simpa using congrArg (mark ++ ·) ih

/-! ### Conjoining tests on canonical pairs -/

private def unframeBits : List Bool → List Bool :=
  blocks [] (fun b => [b]) (fun _ => [])

private theorem unframeBits_encode (x : List Bool) : unframeBits (bitEncode x) = x := by
  rw [DenseSAT.Converter.bitEncode_list]
  induction x with
  | nil => rfl
  | cons b x ih =>
    change unframeBits (delimit [b] ++ DenseSAT.Converter.encSnd x) = b :: x
    unfold unframeBits at ih ⊢
    rw [blocks_frame, ih]
    rfl

/-- The conjunction of two polynomial-time tests on the same pair of bit strings takes
polynomial time in the canonical pair encoding. -/
theorem polyCombinePair {f g : List Bool × List Bool → Bool} (hf : IsPolyTime f)
    (hg : IsPolyTime g) : IsPolyTime (fun q => f q && g q) := by
  let unpack (s : List Bool) := (unframeBits (field true false s), unframeBits (field false true s))
  have hu : IsPolyTime unframeBits := polyBlocks _ _ _
  have hp : IsPolyTime unpack :=
    polyPair ((polyField _ _).comp hu) ((polyField _ _).comp hu)
  have hid (q : List Bool × List Bool) : unpack (bitEncode q) = q := by
    rcases q with ⟨x, y⟩
    change (unframeBits (field _ _ (delimit (bitEncode x) ++ bitEncode y)),
      unframeBits (field _ _ (delimit (bitEncode x) ++ bitEncode y))) = _
    simp [field_delimit, unframeBits_encode]
  have hr := IsPolyTime.combine Bool.and (hp.comp hf) (hp.comp hg)
  obtain ⟨m⟩ := hr
  obtain ⟨mach⟩ := tm2ComputableInPolyTime_comp (f := id)
    (g := fun s => f (unpack s) && g (unpack s)) DenseSAT.EncodeBits.computable m
  refine ⟨{ mach with outputsFun := fun q => ?_ }⟩
  have h := mach.outputsFun (bitEncode q)
  simp only [comp_apply, id_eq, hid] at h
  exact h

/-! ### Checking raw framing -/

/-- State 0 begins a frame, 1 expects a marker inside a frame, and 2 expects a payload bit.
State 3 skips the suffix after the first complete frame in single-frame mode. -/
private def synStep (many : Bool) (q : Fin 4) (b : Bool) : Fin 4 × List Bool :=
  (if q = 3 then 3 else if q = 2 then 1 else if b then 2 else if many then 0 else 3, [])

private def syntaxFlag (many : Bool) (q : Fin 4) :=
  scan (synStep many) (fun s => [decide (s = if many then 0 else 3)]) q

private theorem syntax_frame (many : Bool) (p r : List Bool) (q : Fin 4) (hq : q < 2) :
    syntaxFlag many q (delimit p ++ r) = syntaxFlag many (if many then 0 else 3) r := by
  induction p generalizing q with
  | nil => fin_cases q <;> simp_all [syntaxFlag, scan, synStep, delimit]
  | cons b p ih =>
    have h := ih 1 (by decide)
    fin_cases q <;> simp_all [delimit, syntaxFlag, scan, synStep]

private theorem syntax_bad (many : Bool) (x : List Bool) (h : undelimit x = none)
    (q : Fin 4) (hq : q < 2) (hne : many = true → q = 0 → x ≠ []) :
    syntaxFlag many q x = [false] := by
  induction x using undelimit.induct generalizing q with
  | case1 r => simp [undelimit] at h
  | case2 b r ih =>
    have hr : undelimit r = none := by simpa [undelimit] using h
    have hi := ih hr 1 (by decide) (by simp)
    fin_cases q <;> simp_all [syntaxFlag, scan, synStep]
  | case3 x h₁ h₂ =>
    have hx : x = [] ∨ x = [true] := by
      cases x with
      | nil => simp
      | cons b xs => cases b <;> cases xs <;> simp_all
    rcases hx with rfl | rfl <;> fin_cases q <;> cases many <;>
      simp_all [syntaxFlag, scan, synStep]

private theorem syntax_one (x : List Bool) : syntaxFlag false 0 x = [(undelimit x).isSome] := by
  cases h : undelimit x with
  | none => exact syntax_bad false x h 0 (by decide) (by simp)
  | some pair =>
    obtain ⟨p, r⟩ := pair
    rw [(Cslib.CookLevin.undelimit_eq_some_iff _ _ _).mp h, syntax_frame _ _ _ _ (by decide)]
    clear h
    induction r with
    | nil => rfl
    | cons b r ih => simpa [syntaxFlag, scan, synStep] using ih

private theorem syntax_list_aux (fuel : ℕ) (x : List Bool) (hx : x.length ≤ fuel) :
    syntaxFlag true 0 x = [(undelimitBlocksAux fuel x).isSome] := by
  induction fuel generalizing x with
  | zero => obtain rfl : x = [] := List.eq_nil_of_length_eq_zero (by omega); rfl
  | succ n ih =>
    cases x with
    | nil => rfl
    | cons b x =>
      unfold undelimitBlocksAux
      cases h : undelimit (b :: x) with
      | none => exact syntax_bad true _ h _ (by decide) (by simp)
      | some pair =>
        obtain ⟨p, r⟩ := pair
        have he := (Cslib.CookLevin.undelimit_eq_some_iff _ _ _).mp h
        rw [he, syntax_frame _ _ _ _ (by decide)]
        have hr : r.length ≤ n := by
          rw [he, List.length_append, length_delimit] at hx
          omega
        simpa using ih r hr

/-- The empty suffix on a well-framed list; otherwise the singleton `[true]`, which cannot be
the final bit of a valid frame sequence. -/
@[expose] def listRejectSuffix (x : List Bool) : List Bool :=
  if (undelimitBlocks x).isSome then [] else [true]

/-- Computing the rejection suffix for a raw sequence of frames takes polynomial time. -/
theorem polyListRejectSuffix : IsPolyTime listRejectSuffix := by
  let mark (_ : Unit) (b : Bool) : Unit × List Bool := ((), if b then [] else [true])
  have h : scan mark (fun _ => []) () ∘ syntaxFlag true 0 = listRejectSuffix := by
    funext x
    change scan mark _ _ (syntaxFlag true 0 x) = _
    rw [syntax_list_aux x.length x le_rfl]
    change scan mark _ _ [(undelimitBlocks x).isSome] = _
    cases hx : undelimitBlocks x <;> simp [listRejectSuffix, hx, scan, mark]
  exact h ▸ (polyScan (synStep true) _ (0 : Fin 4)).comp (polyScan mark _ ())

/-- Testing whether the first frame is complete takes polynomial time. The suffix after a
complete frame need not be framed. -/
theorem polyUndelimitIsSome : IsPolyTime (fun x => (undelimit x).isSome) := by
  have head : IsPolyTime (fun x : List Bool => x.headD false) :=
    isPolyTime_dup.comp (isPolyTime_heads fun a _ => a)
  have h := (polyScan (synStep false) _ (0 : Fin 4)).comp head (f := syntaxFlag false 0)
  simpa [Function.comp_def, syntax_one] using h

/-- Testing whether the entire bit string is a sequence of complete frames takes polynomial
time. -/
theorem polyUndelimitBlocksIsSome : IsPolyTime (fun x => (undelimitBlocks x).isSome) := by
  have head : IsPolyTime (fun x : List Bool => x.headD false) :=
    isPolyTime_dup.comp (isPolyTime_heads fun a _ => a)
  have h := (polyScan (synStep true) _ (0 : Fin 4)).comp head (f := syntaxFlag true 0)
  have he (x : List Bool) : syntaxFlag true 0 x = [(undelimitBlocks x).isSome] :=
    syntax_list_aux x.length x le_rfl
  simpa [Function.comp_def, he] using h

end Cslib.Complexity.PolynomialEncoding.StreamScan
