/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
import CSLibExt.Computability.Complexity.PolynomialEncoding.BitOperations
import Mathlib.Tactic.FinCases
import CSLibExt.Computability.Complexity.FramedCNF.NormalizeMachine
import CSLibExt.Computability.Complexity.PairProjection
import CSLibExt.Computability.Complexity.BoolClosure
import CSLibExt.Computability.Complexity.Karp.SubsetSumComplete
import CSLibExt.Computability.Complexity.PolynomialEncoding.ListNat
import CSLibExt.Computability.Complexity.PolynomialEncoding.UnaryNat

/-!
# NP-completeness of exact-cardinality subset sum

A single selection mask verifies both the sum and the number of selected entries.
Zero-padding reduces ordinary subset sum to the exact-cardinality problem.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CardinalitySubsetSum

/-- **Exact-cardinality subset-sum instances.** An exact-cardinality subset-sum instance is a
triple $(a, K, T)$ consisting of a list $a$ of natural numbers, a natural number $K$ (the
cardinality) and a natural number $T$ (the target). -/
abbrev CardinalitySubsetSumInstance := List ℕ × ℕ × ℕ

/-- **Feasibility of an exact-cardinality subset-sum instance.** An exact-cardinality subset-sum
instance $(a, K, T)$ is feasible when some subsequence of the list $a$ (entries kept in order, not
necessarily contiguous) has exactly $K$ entries and sum $T$. -/
def CardinalitySubsetSumFeasible
    (i : CardinalitySubsetSumInstance) : Prop :=
  ∃ s : List ℕ, s.Sublist i.1 ∧ s.length = i.2.1 ∧ s.sum = i.2.2

open Classical in
/-- **Exact-cardinality subset sum as a decision problem.** The decision problem
EXACT-CARDINALITY SUBSET SUM accepts a bitstring $x$ exactly when $x$ decodes, under the canonical
bitstring encoding, to an exact-cardinality subset-sum instance that is feasible; it rejects every
bitstring that does not decode. -/
noncomputable def cardinalitySubsetSumDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CardinalitySubsetSumInstance) x with
  | some i => decide (CardinalitySubsetSumFeasible i)
  | none => false

open ComplexityTheory BitstringEncoding Computability Turing Function TM2Program
open Cslib.Complexity Cslib.Complexity.Karp

private abbrev Bits := List Bool

/-! ### Polynomial-time streaming passes on the raw input -/

open Cslib.Complexity.PolynomialEncoding.BitScan

private def unframeBits := scan
  (fun (payload b : Bool) => if payload then (false, [b]) else (b, [])) (fun _ => []) false

private theorem unframeBits_encode (x : Bits) : unframeBits (bitEncode x) = x := by
  rw [DenseSAT.Converter.bitEncode_list]
  induction x with
  | nil => rfl
  | cons b x ih => simpa [unframeBits, DenseSAT.Converter.encSnd, scan] using ih

private theorem polyCombinePair {f g : Bits × Bits → Bool} (hf : IsPolyTime f)
    (hg : IsPolyTime g) : IsPolyTime (fun q => f q && g q) := by
  let unpack (s : Bits) := (unframeBits (field true false s), unframeBits (field false true s))
  have hu : IsPolyTime unframeBits := polyScan _ _ _
  have hp : IsPolyTime unpack :=
    polyPair ((polyField _ _).comp hu) ((polyField _ _).comp hu)
  have hid (q : Bits × Bits) : unpack (bitEncode q) = q := by
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

private theorem polyFramedLength : IsPolyTime (fun x : Bits => delimit (encodeNat x.length)) := by
  let c := PolynomialEncoding.UnaryNat.component true
  apply Host.isPolyTime_reduction (c := c) (cX := EmitSS.K.A) (cO := EmitSS.K.O)
    (gX := fun _ => EmitSS.U) (start := .emit .hv) (done := .done) (Equiv.refl Bool)
    _ (Polynomial.C 708 * Polynomial.X + Polynomial.C 304) rfl
  intro x
  let S := update (fun k : EmitSS.K => ([] : List (EmitSS.Γ k))) .A (x.map fun _ => EmitSS.U)
  obtain ⟨U, hr, ho, _⟩ := PolynomialEncoding.UnaryNat.run_framed x.length [] false S
    (by simp [S, cnt]) (by simp [S]) (by simp [S]) (by simp [S])
  exact ⟨false, U, by simpa [c, S, PolynomialEncoding.UnaryNat.component] using hr,
    by change U .O = List.map id _; simpa using ho⟩

/-! ### Reading framed lists and checking the instance syntax -/

/-- The state records whether a payload bit is due and whether its last bit was zero.
The latter determines whether the binary decoder supplies an implicit final one. -/
private def blockStep (bit : Bool → Bits) (close : Bool → Bits)
    (q : Bool × Bool) (b : Bool) : (Bool × Bool) × Bits :=
  if q.1 then ((false, !b), bit b)
  else if b then ((true, q.2), []) else ((false, false), close q.2)

private def blocks (bit : Bool → Bits) (close : Bool → Bits) :=
  scan (blockStep bit close) (fun _ => []) (false, false)

private theorem blocks_frame (bit : Bool → Bits) (close : Bool → Bits) (p r : Bits)
    (last : Bool) :
    scan (blockStep bit close) (fun _ => []) (false, last) (delimit p ++ r) =
      p.flatMap bit ++ close ((p.getLast?.map (!·)).getD last) ++ blocks bit close r := by
  induction p generalizing last with
  | nil => simp [scan, delimit, blocks, blockStep]
  | cons b p ih =>
    simp only [delimit, List.cons_append, scan, blockStep, Bool.false_eq_true, ↓reduceIte,
      List.nil_append, List.flatMap_cons, List.append_assoc, ih]
    cases p with
    | nil => rfl
    | cons c cs =>
      obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp
        (show (c :: cs).getLast?.isSome by simp)
      simp [hd]

private def normList := blocks (fun b => [true, b])
  (fun extra => if extra then [true, true, false] else [false])

private def marks (mark : Bits) := blocks (fun _ => []) (fun _ => mark)

private theorem normList_frames (ps : List Bits) :
    normList (ps.map delimit).flatten = bitEncode (ps.map decodeNat) := by
  rw [PolynomialEncoding.encode_decoded_nat_blocks]
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons, List.flatten_cons]
    unfold normList blocks at ih ⊢
    rw [blocks_frame]
    change _ ++ _ ++ scan _ _ _ _ = _
    rw [← ih]
    simp only [List.append_assoc]
    rw [DenseSAT.Converter.delimit_eq, FramedCNF.normalizeNat]
    cases hl : p.getLast? with
    | none => simp
    | some b => cases b <;> simp [List.append_assoc]

private theorem marks_frames (ps : List Bits) (mark : Bits) :
    marks mark (ps.map delimit).flatten = (List.replicate ps.length mark).flatten := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_cons, List.replicate_succ]
    change scan _ _ _ (delimit p ++ _) = _
    rw [blocks_frame]
    have hempty : p.flatMap (fun _ => ([] : Bits)) = [] := by induction p <;> simp_all
    simp [hempty, ← ih, marks]

/-- State 0 begins a frame, 1 expects a marker inside a frame, and 2 expects a payload bit.
State 3 skips the suffix after the first complete frame in single-frame mode. -/
private def synStep (many : Bool) (q : Fin 4) (b : Bool) : Fin 4 × Bits :=
  (if q = 3 then 3 else if q = 2 then 1 else if b then 2 else if many then 0 else 3, [])

private def syntaxFlag (many : Bool) (q : Fin 4) :=
  scan (synStep many) (fun s => [decide (s = if many then 0 else 3)]) q

private theorem syntax_frame (many : Bool) (p r : Bits) (q : Fin 4) (hq : q < 2) :
    syntaxFlag many q (delimit p ++ r) = syntaxFlag many (if many then 0 else 3) r := by
  induction p generalizing q with
  | nil => fin_cases q <;> simp_all [syntaxFlag, scan, synStep, delimit]
  | cons b p ih =>
    have h := ih 1 (by decide)
    fin_cases q <;> simp_all [delimit, syntaxFlag, scan, synStep]

private theorem syntax_bad (many : Bool) (x : Bits) (h : undelimit x = none)
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

private theorem syntax_one (x : Bits) : syntaxFlag false 0 x = [(undelimit x).isSome] := by
  cases h : undelimit x with
  | none => exact syntax_bad false x h 0 (by decide) (by simp)
  | some pair =>
    obtain ⟨p, r⟩ := pair
    rw [(Cslib.CookLevin.undelimit_eq_some_iff _ _ _).mp h, syntax_frame _ _ _ _ (by decide)]
    clear h
    induction r with
    | nil => rfl
    | cons b r ih => simpa [syntaxFlag, scan, synStep] using ih

private theorem syntax_list_aux (fuel : ℕ) (x : Bits) (hx : x.length ≤ fuel) :
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

private def valid (x : Bits) :=
  (undelimit x).isSome && (undelimit (field false true x)).isSome &&
    (undelimitBlocks (field true false x)).isSome

private theorem polyValid : IsPolyTime valid := by
  have head : IsPolyTime (fun x : Bits => x.headD false) :=
    isPolyTime_dup.comp (isPolyTime_heads fun a _ => a)
  have h₁ : IsPolyTime (fun x : Bits => (undelimit x).isSome) := by
    have h := (polyScan (synStep false) _ (0 : Fin 4)).comp head
      (f := syntaxFlag false 0)
    simpa [Function.comp_def, syntax_one] using h
  have hl : IsPolyTime (fun x : Bits => (undelimitBlocks x).isSome) := by
    have h := (polyScan (synStep true) _ (0 : Fin 4)).comp head
      (f := syntaxFlag true 0)
    have he (x : Bits) : syntaxFlag true 0 x = [(undelimitBlocks x).isSome] :=
      syntax_list_aux x.length x le_rfl
    simpa [Function.comp_def, he] using h
  exact (h₁.combine Bool.and ((polyField false true).comp h₁)).combine Bool.and
    ((polyField true false).comp hl)

private def rawInstance (ps : List Bits) (k t : Bits) : Bits :=
  delimit (ps.map delimit).flatten ++ (delimit k ++ t)

private theorem decode_raw (ps : List Bits) (k t : Bits) :
    bitDecode (α := CardinalitySubsetSumInstance) (rawInstance ps k t) =
      some (ps.map decodeNat, decodeNat k, decodeNat t) := by
  have h : bitDecode (α := List ℕ) (ps.map delimit).flatten = some (ps.map decodeNat) := by
    simp [PolynomialEncoding.decode_list_nat, undelimitBlocks_flatten_delimit]
  have pair {α β : Type} [BitstringEncoding α] [BitstringEncoding β]
      {a : α} {b : β} {p r : Bits} (ha : bitDecode p = some a) (hb : bitDecode r = some b) :
      bitDecode (delimit p ++ r) = some (a, b) := by
    unfold bitDecode BitstringEncoding.instProd
    simp [ha, hb]
  exact pair h (pair (p := k) (r := t) rfl rfl)

private theorem valid_iff_raw (x : Bits) :
    valid x = true ↔ ∃ ps k t, x = rawInstance ps k t := by
  constructor
  · intro h
    obtain ⟨⟨ha, hb⟩, hc⟩ := (show (_ ∧ _) ∧ _ by simpa [valid] using h)
    obtain ⟨⟨p, r⟩, hp⟩ := Option.isSome_iff_exists.mp ha
    obtain rfl := (Cslib.CookLevin.undelimit_eq_some_iff _ _ _).mp hp
    simp only [field_delimit, ↓reduceIte, Bool.false_eq_true, List.nil_append,
      List.append_nil] at hb hc
    obtain ⟨⟨k, t⟩, hk⟩ := Option.isSome_iff_exists.mp hb
    obtain ⟨ps, hs⟩ := Option.isSome_iff_exists.mp hc
    exact ⟨ps, k, t, by rw [PolynomialEncoding.blocks_decode_sound hs,
      (Cslib.CookLevin.undelimit_eq_some_iff _ _ _).mp hk]; rfl⟩
  · rintro ⟨ps, k, t, rfl⟩
    simp [valid, rawInstance, field_delimit, undelimitBlocks_flatten_delimit]

private theorem invalid_decode {x : Bits} (hv : valid x ≠ true) :
    bitDecode (α := CardinalitySubsetSumInstance) x = none := by
  cases hd : bitDecode (α := CardinalitySubsetSumInstance) x with
  | none => rfl
  | some i =>
    obtain ⟨as, k, t⟩ := i
    obtain ⟨p, r, he, hp, hr⟩ := PolynomialEncoding.decoded_pair_parts hd
    obtain ⟨kp, tp, he', _, _⟩ := PolynomialEncoding.decoded_pair_parts hr
    rw [PolynomialEncoding.decode_list_nat] at hp
    obtain ⟨ps, hs, _⟩ := Option.map_eq_some_iff.mp hp
    exact (hv ((valid_iff_raw x).2 ⟨ps, kp, tp, by
      rw [he, he', PolynomialEncoding.blocks_decode_sound hs]; rfl⟩)).elim

/-- Build a SUBSET SUM verifier input for either the values or their selection count. -/
private def checkInput (count : Bool) (x : Bits) : Bits :=
  let items := field true false x
  let fields := field false true x
  let target := field count (!count) fields
  delimit (FramedCNF.normalizeNat target) ++
    (if count then marks (delimit (encodeNat 1)) items else normList items)

private theorem polyCheckInput (count : Bool) : IsPolyTime (checkInput count) := by
  apply polyAppend
    ((((polyField false true).comp (polyField count (!count))).comp
      FramedCNF.NormalizeMachine.isPolyTime_normalizeNat).comp polyDelimit)
  cases count <;> exact (polyField true false).comp (polyScan _ _ _)

private theorem checkInput_raw (count : Bool) (ps : List Bits) (k t : Bits) :
    checkInput count (rawInstance ps k t) =
      encodeSS (if count then List.replicate ps.length 1 else ps.map decodeNat)
        (decodeNat (if count then k else t)) := by
  have he (as : List ℕ) : bitEncode as = as.flatMap (fun n => delimit (encodeNat n)) := by
    change ((as.map encodeNat).map delimit).flatten = _
    simp [List.flatMap_def, Function.comp_def]
  cases count <;> simp [checkInput, rawInstance, field_delimit, marks_frames, normList_frames,
    FramedCNF.normalizeNat_eq_encode_decode, encodeSS, he, List.flatMap_def]

private def verify (q : Bits × Bits) : Bool :=
  (valid q.1 && SSVerify.ssCheck (checkInput false q.1) q.2) &&
    SSVerify.ssCheck (checkInput true q.1) q.2

private theorem polyVerify : IsPolyTime verify := by
  have each (c : Bool) := (polyCheckInput c).map_fst.comp isPolyTime_ssCheck
  exact polyCombinePair (polyCombinePair (isPolyTime_fst.comp polyValid) (each false)) (each true)

private theorem count_pick (as : List ℕ) (w : Bits) :
    (SSVerify.pick (List.replicate as.length 1) w).sum = (SSVerify.pick as w).length := by
  induction as generalizing w with
  | nil => rfl
  | cons a as ih =>
    cases h : (w.head?).getD false <;>
      simp [SSVerify.pick, List.replicate_succ, h, ih, Nat.add_comm]

private theorem ssCheck_encode (as : List ℕ) (t : ℕ) (w : Bits) :
    SSVerify.ssCheck (encodeSS as t) w = true ↔ (SSVerify.pick as w).sum = t := by
  simp [SSVerify.ssCheck, SSVerify.decodeSS_eq_some.mpr (rfl : encodeSS as t = _)]

private theorem membership : cardinalitySubsetSumDec ∈ NP := by
  refine ⟨Polynomial.X, verify, polyVerify, fun x => ?_⟩
  by_cases hv : valid x = true
  · obtain ⟨ps, k, t, rfl⟩ := (valid_iff_raw x).mp hv
    let as := ps.map decodeNat
    have hw (w : Bits) : verify (rawInstance ps k t, w) = true ↔
        (SSVerify.pick as w).sum = decodeNat t ∧ (SSVerify.pick as w).length = decodeNat k := by
      have hc := count_pick as w
      simp only [as, List.length_map] at hc
      simp [verify, hv, checkInput_raw, ssCheck_encode, hc, as]
    simp only [cardinalitySubsetSumDec, decode_raw, decide_eq_true_eq, Polynomial.eval_X, hw]
    constructor
    · rintro ⟨s, hs, hk, ht⟩
      obtain ⟨w, hlen, hsel⟩ := SSVerify.exists_pick hs
      refine ⟨w, ?_, hsel ▸ ht, hsel ▸ hk⟩
      have := length_le_length_flatten_delimit ps
      simp only [hlen, List.length_map, rawInstance, List.length_append, length_delimit]
      omega
    · rintro ⟨w, _, ht, hk⟩
      exact ⟨SSVerify.pick as w, SSVerify.pick_sublist _ _, hk, ht⟩
  · simp [cardinalitySubsetSumDec, invalid_decode hv, verify, hv]

/-! ### Padding ordinary SUBSET SUM instances -/

private theorem feasible_pad (as : List ℕ) (t : ℕ) :
    CardinalitySubsetSumFeasible (as ++ List.replicate as.length 0, as.length, t) ↔
      ∃ s : List ℕ, s.Sublist as ∧ s.sum = t := by
  constructor
  · rintro ⟨s, hs, _, ht⟩
    obtain ⟨a, z, rfl, ha, hz⟩ := List.sublist_append_iff.mp hs
    obtain ⟨n, _, rfl⟩ := List.sublist_replicate_iff.mp hz
    exact ⟨a, ha, by simpa using ht⟩
  · rintro ⟨s, hs, ht⟩
    let n := as.length - s.length
    have hn : n ≤ as.length := Nat.sub_le _ _
    refine ⟨s ++ List.replicate n 0, hs.append ((List.replicate_sublist_replicate 0).mpr hn),
      ?_, by simpa using ht⟩
    simp only [List.length_append, List.length_replicate, n]
    have := hs.length_le
    omega

private def pad (x : Bits) : Bits :=
  let items := field false true x
  let zeros := marks [false] items
  delimit (items ++ zeros) ++ (delimit (encodeNat zeros.length) ++ field true false x)

private theorem polyPad : IsPolyTime pad := by
  have hi := polyField false true
  have hz : IsPolyTime (fun x => marks [false] (field false true x)) := hi.comp (polyScan _ _ _)
  exact polyAppend ((polyAppend hi hz).comp polyDelimit)
    (polyAppend (hz.comp polyFramedLength) (polyField true false))

private theorem pad_encode (as : List ℕ) (t : ℕ) :
    pad (encodeSS as t) =
      bitEncode (as ++ List.replicate as.length 0, as.length, t) := by
  let ps := as.map encodeNat
  have he : encodeSS as t = delimit (encodeNat t) ++ (ps.map delimit).flatten := by
    simp [encodeSS, ps, List.flatMap_def, Function.comp_def]
  have hz : marks [false] (ps.map delimit).flatten = List.replicate as.length false := by
    rw [marks_frames, List.flatten_replicate_singleton, List.length_map]
  change pad (encodeSS as t) = delimit
    ((((as ++ List.replicate as.length 0).map encodeNat).map delimit).flatten) ++
      (delimit (encodeNat as.length) ++ encodeNat t)
  simp only [pad, he, field_delimit, Bool.false_eq_true, ↓reduceIte, List.append_nil,
    List.nil_append, hz, List.length_replicate, List.map_append, List.flatten_append,
    List.map_replicate]
  rw [show delimit (encodeNat 0) = [false] from rfl, List.flatten_replicate_singleton]

private theorem pad_correct (as : List ℕ) (t : ℕ) :
    subsetSumDec (encodeSS as t) = cardinalitySubsetSumDec (pad (encodeSS as t)) := by
  apply Bool.eq_iff_iff.mpr
  rw [subsetSumDec_encodeSS_eq_true, pad_encode]
  simp [cardinalitySubsetSumDec, feasible_pad]

/-- The VERTEX COVER reduction emits a canonical SUBSET SUM instance on every input.
Consequently padding only needs its semantic correctness on canonical instances. -/
private theorem hardness : NPHard cardinalitySubsetSumDec := by
  apply NPHard.of_polyManyOneRed vertexCoverDec_npHard
  refine ⟨pad ∘ reduceSS, isPolyTime_reduceSS.comp polyPad, fun x => ?_⟩
  rw [vertexCoverDec_eq_subsetSumDec_reduceSS]
  have h : ∃ as t, reduceSS x = encodeSS as t := by
    unfold reduceSS
    split
    · split
      · exact ⟨_, _, rfl⟩
      · exact ⟨[], 1, rfl⟩
    · exact ⟨[], 1, rfl⟩
  obtain ⟨as, t, hs⟩ := h
  simpa [comp_apply, hs] using pad_correct as t

/-- **EXACT-CARDINALITY SUBSET SUM is NP-complete.** The decision problem EXACT-CARDINALITY
SUBSET SUM lies in NP, and every decision problem in NP has a polynomial-time many-one reduction
to it.

Source: M. R. Garey and D. S. Johnson,
*Computers and Intractability* (1979), SUBSET SUM; NP-completeness via the zero-padding
reduction from ordinary subset sum. -/
public theorem cardinalitySubsetSum_npComplete :
    cardinalitySubsetSumDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L cardinalitySubsetSumDec :=
  ⟨membership, hardness⟩

end MetaMathlibExt.Complexity.NPComplete.CardinalitySubsetSum
