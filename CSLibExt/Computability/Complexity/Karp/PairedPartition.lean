/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
import CSLibExt.Computability.Complexity.BoolClosure
import CSLibExt.Computability.Complexity.Karp.PartitionComplete
import Mathlib.Tactic.FinCases

/-!
# PARTITION choosing one element of each pair is NP-complete

INSTANCE: a finite set `A = {a₁, a₂, ..., a₂ₙ}` and a size `s(a) ∈ ℤ⁺` for each `a ∈ A`.
QUESTION: is there a subset `A' ⊆ A` containing exactly one of `a₂ᵢ₋₁, a₂ᵢ` for `1 ≤ i ≤ n`
such that `∑_{a ∈ A'} s(a) = ∑_{a ∈ A - A'} s(a)`?

The instance is the list of the `n` pairs `(s(a₂ᵢ₋₁), s(a₂ᵢ))`. A subset `A'` containing exactly
one element of each pair is a list of `n` choices (`true` picks `a₂ᵢ₋₁`, `false` picks `a₂ᵢ`); the
two sums are equal exactly when the sum over `A'` is half the total.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).

The hardness map adds one to each original weight and pairs it with one.
For membership, a streamed expansion of the choice bits supplies selection masks to the
SUBSET-SUM verifier. A separate check on unit weights ensures no pair was skipped.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PairedPartition

/-- An instance: the pairs `[(s(a₁), s(a₂)), ..., (s(a₂ₙ₋₁), s(a₂ₙ))]`. -/
abbrev PairedPartitionInstance := List (ℕ × ℕ)

/-- Well-formedness of an instance: every size is positive. -/
def WellFormed (i : PairedPartitionInstance) : Prop :=
  ∀ p ∈ i, 0 < p.1 ∧ 0 < p.2

/-- The size of the element chosen from a pair: the first if `b`, the second otherwise. -/
def chosen (p : ℕ × ℕ) (b : Bool) : ℕ :=
  if b then p.1 else p.2

/-- One element chosen from each pair, with the chosen sizes summing to half the total. -/
def PairedPartitionFeasible (i : PairedPartitionInstance) : Prop :=
  ∃ c : List Bool, c.length = i.length ∧
    (List.zipWith chosen i c).sum * 2 = (i.map fun p => p.1 + p.2).sum

open Classical in
/-- PARTITION choosing one element of each pair as a decision problem over bitstrings. -/
noncomputable def pairedPartitionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PairedPartitionInstance) x with
  | some i => decide (WellFormed i ∧ PairedPartitionFeasible i)
  | none => false

open ComplexityTheory BitstringEncoding Computability Turing Function TM2Program
open Cslib.Complexity Cslib.Complexity.Karp Cslib.Complexity.PolynomialEncoding

private abbrev Bits := List Bool

/-! ### Finite-state string passes

The scanner and its polynomial-time proof follow `Karp.CardinalitySubsetSum`.
-/

private def scan {Q : Type} (step : Q → Bool → Q × Bits) (finish : Q → Bits)
    (q : Q) : Bits → Bits
  | [] => finish q
  | b :: x => (step q b).2 ++ scan step finish (step q b).1 x

/-- A finite-state scan stores output in reverse order and reverses it once at the end. -/
private theorem polyScan {Q : Type} [Finite Q]
    (step : Q → Bool → Q × Bits) (finish : Q → Bits) (q₀ : Q) :
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
  let st (x r o : Bits) (k : Fin 3) : Bits := if k = 0 then x else if k = 1 then r else o
  have up0 (x r o l : Bits) : update (st x r o) 0 l = st l r o := by
    funext k
    fin_cases k <;> rfl
  have up1 (x r o l : Bits) : update (st x r o) 1 l = st x l o := by
    funext k
    fin_cases k <;> rfl
  have hr (x : Bits) (q : Q) (v : Bool) (r : Bits) :
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
  have bound (x : Bits) (q : Q) : (scan step finish q x).length ≤ (x.length + 1) * B := by
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
    (st [] y.reverse []) (by simp [st]) (by simp [IsBitBlock]) (by simp [EndsBitBlock])
  have hi : update (fun _ : Fin 3 => ([] : Bits)) 0 x = st x [] [] := by
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

private theorem polyPair {f g : Bits → Bits} (hf : IsPolyTime f) (hg : IsPolyTime g) :
    IsPolyTime (fun x => (f x, g x)) :=
  ((isPolyTime_dup.comp hg.map_fst).comp isPolyTime_swap).comp hf.map_fst

private theorem polyEncoded {α : Type} [BitstringEncoding α] {f : Bits → Bool}
    (hf : IsPolyTime f) {g : α → Bool} (he : ∀ a, f (bitEncode a) = g a) : IsPolyTime g := by
  obtain ⟨m⟩ := hf
  obtain ⟨mach⟩ := tm2ComputableInPolyTime_comp (f := id) (g := f)
    DenseSAT.EncodeBits.computable m
  refine ⟨{ mach with outputsFun := fun a => ?_ }⟩
  have h := mach.outputsFun (bitEncode a)
  simp only [comp_apply, id_eq, he] at h
  exact h

private def fieldStep (left : Bool) : Option Bool → Bool → Option Bool × Bits
  | none, b => (none, if left then [] else [b])
  | some false, b => (if b then some true else none, [])
  | some true, b => (some false, if left then [b] else [])

private def field (left : Bool) : Bits → Bits :=
  scan (fieldStep left) (fun _ => []) (some false)

private theorem field_delimit (left : Bool) (p r : Bits) :
    field left (delimit p ++ r) = if left then p else r := by
  have tail : scan (fieldStep left) (fun _ => []) none r = if left then [] else r := by
    induction r with
    | nil => cases left <;> rfl
    | cons b r ih => cases left <;> simp_all [scan, fieldStep]
  induction p with
  | nil => simpa [field, delimit, scan, fieldStep] using tail
  | cons b p ih => cases left <;> simp_all [field, delimit, scan, fieldStep]

private def unframe : Bits → Bits := scan
  (fun (due b : Bool) => if due then (false, [b]) else (b, [])) (fun _ => []) false

private theorem unframe_encode (x : Bits) : unframe (bitEncode x) = x := by
  rw [DenseSAT.Converter.bitEncode_list]
  induction x with
  | nil => rfl
  | cons b x ih => simpa [unframe, DenseSAT.Converter.encSnd, scan] using ih

/-! ### Correctness of the instance-level reduction -/

private def fromPartition (as : List ℕ) : PairedPartitionInstance :=
  as.map fun a => (a + 1, 1)

private theorem fromPartition_wellFormed (as : List ℕ) : WellFormed (fromPartition as) := by
  intro p hp
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hp
  simp

private theorem sum_pairs (as : List ℕ) :
    ((fromPartition as).map fun p => p.1 + p.2).sum = as.sum + 2 * as.length := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp only [fromPartition, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    omega

private theorem sum_choices (as : List ℕ) (w : Bits) (h : w.length = as.length) :
    (List.zipWith chosen (fromPartition as) w).sum = (SSVerify.pick as w).sum + as.length := by
  induction as generalizing w with
  | nil => rfl
  | cons a as ih =>
    cases w with
    | nil => simp at h
    | cons b w =>
      have hh := ih w (by simpa using h)
      change (List.zipWith chosen ((a + 1, 1) :: fromPartition as) (b :: w)).sum = _
      rw [SSVerify.sum_pick_cons]
      cases b <;> simp only [List.zipWith_cons_cons, List.sum_cons, List.length_cons, hh,
        List.headD_cons, List.tail_cons, chosen, Bool.false_eq_true, ↓reduceIte] <;> omega

private theorem fromPartition_feasible (as : List ℕ) :
    PairedPartitionFeasible (fromPartition as) ↔ Partition.PartitionFeasible as := by
  constructor
  · rintro ⟨w, h, hs⟩
    have hw : w.length = as.length := by simpa [fromPartition] using h
    rw [sum_choices as w hw, sum_pairs] at hs
    exact ⟨SSVerify.pick as w, SSVerify.pick_sublist _ _, by omega⟩
  · rintro ⟨s, hs, hsum⟩
    obtain ⟨w, hw, rfl⟩ := SSVerify.exists_pick hs
    refine ⟨w, by simpa [fromPartition] using hw, ?_⟩
    rw [sum_choices as w hw, sum_pairs]
    omega

private theorem polyAppend {f g : Bits → Bits} (hf : IsPolyTime f) (hg : IsPolyTime g) :
    IsPolyTime (fun x => f x ++ g x) := by
  apply (polyPair hf hg).comp (g := fun p : Bits × Bits => p.1 ++ p.2)
  let step : Option Bool → Bool → Option Bool × Bits
    | none, b => (none, [b])
    | some false, b => (if b then some true else none, [])
    | some true, b => (some false, [b])
  let f := scan step (fun _ => []) (some false)
  have hc (p r : Bits) : f (delimit p ++ r) = p ++ r := by
    have tail : scan step (fun _ => []) none r = r := by
      induction r with
      | nil => rfl
      | cons b r ih => simp [scan, step, ih]
    induction p with
    | nil => exact tail
    | cons b p ih => simpa [f, scan, step, delimit] using congrArg (b :: ·) ih
  obtain ⟨m⟩ := Preimage.raw_computable (polyScan step _ (some false))
  refine ⟨{ m with outputsFun := fun ⟨x, y⟩ => ?_ }⟩
  have h := m.outputsFun (delimit (bitEncode x) ++ bitEncode y)
  rw [show scan step (fun _ => []) (some false) (delimit (bitEncode x) ++ bitEncode y) =
    bitEncode x ++ bitEncode y from hc _ _] at h
  have he : bitEncode x ++ bitEncode y = bitEncode (x ++ y) := by
    simp only [DenseSAT.Converter.bitEncode_list, DenseSAT.Converter.encSnd, List.flatMap_append]
  rw [he] at h
  exact h

/-! ### Passing through the list framing -/

/-- The outer frame scanner delivers only payload bits to the inner transducer.
A failed close (or truncated frame) does not leave the scanner at a block boundary. -/
private inductive Frame (Q : Type)
  | boundary | mark (q : Q) | bit (q : Q) | bad

private instance {Q : Type} [Finite Q] : Finite (Frame Q) := by
  let f : Frame Q → Option (Option (Bool × Q))
    | .boundary => some none
    | .mark q => some (some (false, q))
    | .bit q => some (some (true, q))
    | .bad => none
  exact Finite.of_injective f (by intro a b h; cases a <;> cases b <;> simp_all [f])

private def frameMark {Q : Type} (close : Q → Option Bits) (q : Q) :
    Bool → Frame Q × Bits
  | true => (.bit q, [])
  | false => match close q with
    | some out => (.boundary, out)
    | none => (.bad, [])

private def frameStep {Q : Type} (q₀ : Q) (put : Q → Bool → Q × Bits)
    (close : Q → Option Bits) : Frame Q → Bool → Frame Q × Bits
  | .boundary => frameMark close q₀
  | .mark q => frameMark close q
  | .bit q => fun b => (.mark (put q b).1, (put q b).2)
  | .bad => fun _ => (.bad, [])

private def frameEnd {Q : Type} (ok fail : Bits) : Frame Q → Bits
  | .boundary => ok
  | _ => fail

private theorem scan_frame {Q : Type} (q₀ : Q) (put : Q → Bool → Q × Bits)
    (close : Q → Option Bits) (f : Frame Q → Bits) (p r : Bits) :
    scan (frameStep q₀ put close) f .boundary (delimit p ++ r) =
      scan put (fun q =>
        (frameMark close q false).2 ++
          scan (frameStep q₀ put close) f (frameMark close q false).1 r) q₀ p := by
  have aux (q : Q) :
      scan (frameStep q₀ put close) f (.mark q) (delimit p ++ r) =
        scan put (fun q =>
          (frameMark close q false).2 ++
            scan (frameStep q₀ put close) f (frameMark close q false).1 r) q p := by
    induction p generalizing q with
    | nil => rfl
    | cons b p ih => simp [delimit, scan, frameStep, frameMark, ih]
  cases p <;> exact aux q₀

private theorem scan_bad {Q : Type} (q₀ : Q) (put : Q → Bool → Q × Bits)
    (close : Q → Option Bits) (ok fail : Bits) (x : Bits) :
    scan (frameStep q₀ put close) (frameEnd ok fail) .bad x = fail := by
  induction x with
  | nil => rfl
  | cons b x ih => simpa only [scan, frameStep, List.nil_append] using ih

/-- A syntactic pass emits no chunks; an unterminated frame therefore returns only failure. -/
private theorem scan_unterminated {Q : Type} (q₀ : Q) (put : Q → Bool → Q)
    (close : Q → Option Bits) (ok fail : Bits) (x : Bits) (h : undelimit x = none)
    (hx : x ≠ []) :
    scan (frameStep q₀ (fun q b => (put q b, [])) close) (frameEnd ok fail) .boundary x =
      fail := by
  have aux : ∀ (l : Bits) (q : Q), undelimit l = none →
      scan (frameStep q₀ (fun q b => (put q b, [])) close) (frameEnd ok fail) (.mark q) l =
        fail := by
    intro l
    induction l using List.twoStepInduction with
    | nil => intro _ _; rfl
    | singleton a => intro q h; cases a <;> simp_all [undelimit, scan, frameStep, frameMark,
        frameEnd]
    | cons_cons a b l ih _ =>
      intro q h
      cases a with
      | false => simp [undelimit] at h
      | true =>
        simp only [undelimit, Option.map_eq_none_iff] at h
        simpa [scan, frameStep, frameMark] using ih (put q b) h
  cases x with
  | nil => contradiction
  | cons a l => exact aux (a :: l) q₀ h

private def frameCheck {Q : Type} (q₀ : Q) (put : Q → Bool → Q) (good : Q → Bool) : Bits → Bits :=
  scan (frameStep q₀ (fun q b => (put q b, [])) (fun q => if good q then some [] else none))
    (frameEnd [true] [false]) .boundary

private theorem scan_state {Q : Type} (put : Q → Bool → Q) (f : Q → Bits) (q : Q) (x : Bits) :
    scan (fun q b => (put q b, [])) f q x = f (x.foldl put q) := by
  induction x generalizing q with
  | nil => rfl
  | cons b x ih => simpa only [scan, List.nil_append, List.foldl_cons] using ih (put q b)

private theorem frameCheck_eq {Q : Type} (q₀ : Q) (put : Q → Bool → Q) (good : Q → Bool)
    (x : Bits) : frameCheck q₀ put good x =
      [(undelimitBlocks x).any fun ps => ps.all fun p => good (p.foldl put q₀)] := by
  suffices aux : ∀ fuel (x : Bits), x.length ≤ fuel → frameCheck q₀ put good x =
      [(undelimitBlocksAux fuel x).any fun ps => ps.all fun p => good (p.foldl put q₀)] from
    aux x.length x le_rfl
  intro fuel
  induction fuel with
  | zero =>
    intro x hx
    obtain rfl : x = [] := List.eq_nil_of_length_eq_zero (by omega)
    rfl
  | succ fuel ih =>
    intro x hx
    cases x with
    | nil => rfl
    | cons b x =>
      have hblocks : undelimitBlocksAux (fuel + 1) (b :: x) =
          (undelimit (b :: x)).bind (fun a => (undelimitBlocksAux fuel a.2).map (a.1 :: ·)) := by
        cases b <;> rfl
      rw [hblocks]
      cases hu : undelimit (b :: x) with
      | none => exact scan_unterminated _ _ _ _ _ _ hu (by simp)
      | some d =>
        obtain ⟨p, r⟩ := d
        have he := (Cslib.CookLevin.undelimit_eq_some_iff _ _ _).mp hu
        have hr : r.length ≤ fuel := by
          rw [he, List.length_append, length_delimit] at hx
          omega
        have hrun : frameCheck q₀ put good (b :: x) =
            if good (p.foldl put q₀) then frameCheck q₀ put good r else [false] := by
          rw [he]
          unfold frameCheck
          rw [scan_frame, scan_state]
          cases hg : good (p.foldl put q₀) <;>
            simp [frameMark, hg, scan_bad]
        rw [hrun, ih r hr]
        change _ = [((undelimitBlocksAux fuel r).map (p :: ·)).any _]
        cases undelimitBlocksAux fuel r <;> cases hg : good (p.foldl put q₀) <;> simp [hg]

/-! ### The binary hardness map -/

private def increment (carry : Bool) : Bits → Bits
  | [] => if carry then [true] else []
  | b :: p => (b ^^ carry) :: increment (b && carry) p

private theorem increment_false (p : Bits) : increment false p = p := by
  induction p with
  | nil => rfl
  | cons b p ih => cases b <;> simp [increment, ih]

private theorem increment_encode (n : ℕ) : increment true (encodeNat n) = encodeNat (n + 1) := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    by_cases hn : n = 0
    · subst n
      rfl
    · rw [TM2Recursive.encodeNat_eq_cons hn,
        TM2Recursive.encodeNat_eq_cons (by omega : n + 1 ≠ 0)]
      rcases Nat.mod_two_eq_zero_or_one n with h | h
      · have hd : (n + 1) / 2 = n / 2 := by omega
        have hm : (n + 1) % 2 = 1 := by omega
        simp [h, hd, hm, increment, increment_false]
      · have hd : (n + 1) / 2 = n / 2 + 1 := by omega
        have hm : (n + 1) % 2 = 0 := by omega
        simp [h, hd, hm, increment, ih (n / 2) (by omega)]

private def doubleFrameBit (b : Bool) : Bits := [true, true, true, b]

private def incrementPut (q : Bool × Bool) (b : Bool) : (Bool × Bool) × Bits :=
  ((b && q.1, !b), doubleFrameBit (b ^^ q.1))

private def incrementTail (q : Bool × Bool) : Bits :=
  (increment q.1 (if q.2 then [true] else [])).flatMap doubleFrameBit ++
    [true, false, true, true, false]

private def normalizeFrom (lastZero : Bool) (p : Bits) : Bits :=
  p ++ if (p.getLast?.map (!·)).getD lastZero then [true] else []

private theorem normalizeFrom_cons (z b : Bool) (p : Bits) :
    normalizeFrom z (b :: p) = b :: normalizeFrom (!b) p := by
  cases p with
  | nil => cases b <;> rfl
  | cons c p =>
    have h : (c :: p).getLast? ≠ none := by simp
    cases he : (c :: p).getLast? with
    | none => contradiction
    | some a => simp only [normalizeFrom, List.getLast?_cons_cons, he, Option.map_some,
        Option.getD_some, List.cons_append]

private theorem normalizeFrom_start (p : Bits) :
    normalizeFrom false p = FramedCNF.normalizeNat p := by
  unfold normalizeFrom FramedCNF.normalizeNat
  cases p.getLast? with
  | none => simp
  | some b => cases b <;> simp

private theorem scan_increment (c z : Bool) (p r : Bits) :
    scan incrementPut (fun q => incrementTail q ++ r) (c, z) p =
      (increment c (normalizeFrom z p)).flatMap doubleFrameBit ++
        [true, false, true, true, false] ++ r := by
  induction p generalizing c z with
  | nil => rfl
  | cons b p ih =>
    simp only [scan, incrementPut, ih, normalizeFrom_cons, increment, List.flatMap_cons,
      List.append_assoc]

private theorem doubleFrameBit_eq (p : Bits) :
    p.flatMap doubleFrameBit ++ [true, false, true, true, false] =
      delimit (delimit p ++ [true]) := by
  induction p with
  | nil => rfl
  | cons b p ih => simp [doubleFrameBit, delimit, ih]

private def pairedOutput : Bits → Bits :=
  scan (frameStep (true, false) incrementPut (some ∘ incrementTail)) (fun _ => []) .boundary

private theorem pairedOutput_block (p r : Bits) :
    pairedOutput (delimit p ++ r) =
      delimit (bitEncode (decodeNat p + 1, (1 : ℕ))) ++ pairedOutput r := by
  unfold pairedOutput
  rw [scan_frame]
  simp only [frameMark, comp_apply]
  rw [scan_increment, doubleFrameBit_eq, normalizeFrom_start,
    FramedCNF.normalizeNat_eq_encode_decode, increment_encode]
  change delimit (delimit (encodeNat (decodeNat p + 1)) ++ [true]) ++ _ =
    delimit (delimit (bitEncode (decodeNat p + 1)) ++ bitEncode (1 : ℕ)) ++ _
  rw [BinaryNatEncoding.bitEncode_nat, show bitEncode (1 : ℕ) = [true] by decide]

private theorem pairedOutput_list (ps : List Bits) :
    pairedOutput ((ps.map delimit).flatten) = bitEncode (fromPartition (ps.map decodeNat)) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons, List.flatten_cons, pairedOutput_block, ih]
    rfl

private def noPaired : Bits := bitEncode ([(1, 2)] : PairedPartitionInstance)

private def sourceFlag : Bits → Bits := frameCheck () (fun _ _ => ()) (fun _ => true)

private def selectStep : Option Bool → Bool → Option Bool × Bits
  | none, true => (some true, [])
  | none, false => (some false, noPaired)
  | some true, b => (some true, [b])
  | some false, _ => (some false, [])

private theorem select_flag (b : Bool) (r : Bits) :
    scan selectStep (fun _ => []) none (b :: r) = if b then r else noPaired := by
  have aux (c : Bool) : scan selectStep (fun _ => []) (some c) r = if c then r else [] := by
    induction r with
    | nil => cases c <;> rfl
    | cons a r ih => cases c <;> simp [scan, selectStep, ih]
  cases b <;> simp [scan, selectStep, aux]

/-- The reduction checks the raw list framing and otherwise outputs a fixed no-instance. -/
private def reduce (x : Bits) : Bits := scan selectStep (fun _ => []) none
  (sourceFlag x ++ pairedOutput x)

private theorem polyReduce : IsPolyTime reduce :=
  (polyAppend (polyScan ..) (polyScan ..)).comp (polyScan ..)

private theorem reduce_correct (x : Bits) :
    Partition.partitionDec x = pairedPartitionDec (reduce x) := by
  classical
  unfold reduce sourceFlag
  rw [frameCheck_eq]
  cases he : undelimitBlocks x with
  | none =>
    simp only [Option.any_none, List.singleton_append, select_flag, Bool.false_eq_true, ↓reduceIte]
    simp only [Partition.partitionDec, decode_list_nat, he, Option.map_none, noPaired,
      pairedPartitionDec, bitDecode_bitEncode]
    symm
    rw [Bool.eq_false_iff, ne_eq, decide_eq_true_eq]
    rintro ⟨_, w, hw, hs⟩
    cases w with
    | nil => simp at hw
    | cons b w => cases b <;> simp [chosen] at hs
  | some ps =>
    have hx : x = (ps.map delimit).flatten := blocks_decode_sound he
    have hflag : (ps.all fun _ => true) = true := List.all_eq_true.mpr fun _ _ => rfl
    simp only [Option.any_some, hflag, List.singleton_append, select_flag, ↓reduceIte]
    rw [show pairedOutput x = bitEncode (fromPartition (ps.map decodeNat)) from
      hx ▸ pairedOutput_list ps]
    simp [Partition.partitionDec, decode_list_nat, he, pairedPartitionDec,
      fromPartition_wellFormed, fromPartition_feasible]

/-! ### Validating and flattening the paired input -/

-- While reading the first component, the state records whether the next bit is a payload bit
-- and whether any payload bit has been seen. Afterwards it records both nonemptiness flags.
private abbrev PairPhase := (Bool × Bool) ⊕ (Bool × Bool)

private def pairNext : PairPhase → Bool → PairPhase
  | .inl (true, _), _ => .inl (false, true)
  | .inl (false, seen), true => .inl (true, seen)
  | .inl (false, seen), false => .inr (seen, false)
  | .inr (first, _), _ => .inr (first, true)

private def pairGood : PairPhase → Bool
  | .inl _ => false
  | .inr (a, b) => a && b

private def pairStart : PairPhase := .inl (false, false)

private def pairPut (count : Bool) (q : PairPhase) (b : Bool) : PairPhase × Bits :=
  (pairNext q b, if count then [] else match q with
    | .inl (true, _) | .inr _ => [true, b]
    | .inl (false, _) => if b then [] else [false])

private def pairClose (count : Bool) (q : PairPhase) : Option Bits :=
  if pairGood q then some (if count then [true, true, false, true, true, false] else [false])
  else none

private def flatten (count : Bool) : Bits → Bits :=
  scan (frameStep pairStart (pairPut count) (pairClose count)) (fun _ => []) .boundary

private def valid (x : Bits) : Bool := (frameCheck pairStart pairNext pairGood x).headD false

private theorem scan_pair_second (count a b : Bool) (p : Bits) (f : PairPhase → Bits) :
    scan (pairPut count) f (.inr (a, b)) p =
      (if count then [] else p.flatMap fun c => [true, c]) ++
        f (.inr (a, b || !p.isEmpty)) := by
  induction p generalizing b with
  | nil => simp [scan]
  | cons c p ih => cases count <;> simp [scan, pairPut, pairNext, ih, List.flatMap_cons]

private theorem scan_pair_first (count seen : Bool) (p r : Bits) (f : PairPhase → Bits) :
    scan (pairPut count) f (.inl (false, seen)) (delimit p ++ r) =
      (if count then [] else delimit p) ++
        scan (pairPut count) f (.inr (seen || !p.isEmpty, false)) r := by
  induction p generalizing seen with
  | nil => simp [delimit, scan, pairPut, pairNext]
  | cons b p ih => cases count <;> simp [delimit, scan, pairPut, pairNext, ih]

private theorem first_bad (p : Bits) (seen : Bool) (hp : undelimit p = none) :
    pairGood (p.foldl pairNext (.inl (false, seen))) = false := by
  induction p using List.twoStepInduction generalizing seen with
  | nil => rfl
  | singleton b => cases b <;> simp_all [undelimit, pairNext, pairGood]
  | cons_cons a b p ih _ =>
    cases a with
    | false => simp [undelimit] at hp
    | true =>
      simp only [undelimit, Option.map_eq_none_iff] at hp
      exact ih true hp

private theorem frameBits_delimit (r : Bits) :
    (r.flatMap fun b => [true, b]) ++ [false] = delimit r := by
  induction r with
  | nil => rfl
  | cons b r ih => simp [delimit, ih]

private theorem flatten_pair (count : Bool) {p r : Bits} (hp : p ≠ []) (hr : r ≠ [])
    (xs : Bits) : flatten count (delimit (delimit p ++ r) ++ xs) =
      (if count then delimit [true] ++ delimit [true] else delimit p ++ delimit r) ++
        flatten count xs := by
  unfold flatten
  rw [scan_frame]
  change scan (pairPut count) _ (.inl (false, false)) (delimit p ++ r) = _
  rw [scan_pair_first, scan_pair_second]
  have hp' := List.isEmpty_eq_false_iff.mpr hp
  have hr' := List.isEmpty_eq_false_iff.mpr hr
  simp only [hp', hr', Bool.not_false, Bool.false_or]
  cases count with
  | true => rfl
  | false =>
    change delimit p ++ ((r.flatMap fun c => [true, c]) ++ ([false] ++ _)) =
      (delimit p ++ delimit r) ++ _
    rw [← List.append_assoc (r.flatMap fun c => [true, c]) [false], frameBits_delimit,
      List.append_assoc]
    rfl

private theorem decode_pair (s : Bits) : bitDecode (α := ℕ × ℕ) s =
    (undelimit s).map fun p => (decodeNat p.1, decodeNat p.2) := by
  change (match undelimit s with
    | none => none
    | some (p, r) => match some (decodeNat p), some (decodeNat r) with
      | some a, some b => some (a, b)
      | _, _ => none) = _
  cases undelimit s <;> rfl

private theorem decodeNat_pos (p : Bits) : 0 < decodeNat p ↔ p ≠ [] := by
  cases p with
  | nil => simp [decodeNat, decodeNum]
  | cons b p =>
    have h : encodeNat (decodeNat (b :: p)) ≠ [] := by
      rw [← FramedCNF.normalizeNat_eq_encode_decode]
      unfold FramedCNF.normalizeNat
      split_ifs <;> simp
    exact iff_of_true (Nat.pos_of_ne_zero (fun he => h (he ▸ rfl))) (List.cons_ne_nil _ _)

private theorem pairGood_eq (s : Bits) : pairGood (s.foldl pairNext pairStart) =
    (bitDecode (α := ℕ × ℕ) s).any (fun p => decide (0 < p.1 ∧ 0 < p.2)) := by
  rw [decode_pair]
  cases h : undelimit s with
  | none => exact first_bad _ false h
  | some d =>
    obtain ⟨p, r⟩ := d
    rw [(Cslib.CookLevin.undelimit_eq_some_iff _ _ _).mp h]
    have hscan (q : PairPhase) (x : Bits) : scan (pairPut true) (fun q => [pairGood q]) q x =
        [pairGood (x.foldl pairNext q)] := scan_state _ _ _ _
    have he := hscan pairStart (delimit p ++ r)
    rw [pairStart, scan_pair_first, scan_pair_second] at he
    have hn (x : Bits) : (!x.isEmpty) = decide (x ≠ []) := by cases x <;> rfl
    simpa [pairStart, pairGood, decodeNat_pos, hn] using he.symm

private theorem pairs_all (ps : List Bits) :
    (ps.all fun p => pairGood (p.foldl pairNext pairStart)) =
      (ps.mapM (bitDecode (α := ℕ × ℕ))).any
        (fun i => i.all fun p => decide (0 < p.1 ∧ 0 < p.2)) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    rw [List.all_cons, pairGood_eq, ih, List.mapM_cons]
    cases bitDecode (α := ℕ × ℕ) p <;>
      cases ps.mapM (bitDecode (α := ℕ × ℕ)) <;> simp

private theorem valid_eq (x : Bits) : valid x =
    (bitDecode (α := PairedPartitionInstance) x).any
      (fun i => i.all fun p => decide (0 < p.1 ∧ 0 < p.2)) := by
  unfold valid
  rw [frameCheck_eq]
  change (undelimitBlocks x).any _ = ((undelimitBlocks x).bind _).any _
  cases undelimitBlocks x with
  | none => rfl
  | some ps => exact pairs_all ps

private def expand (count : Bool) (i : PairedPartitionInstance) : List ℕ :=
  i.flatMap fun p => if count then [1, 1] else [p.1, p.2]

private theorem expand_cons (count : Bool) (p : ℕ × ℕ) (i : PairedPartitionInstance) :
    expand count (p :: i) = (if count then [1, 1] else [p.1, p.2]) ++ expand count i := rfl

private theorem flatten_spec (count : Bool) (ps : List Bits) {i : PairedPartitionInstance}
    (hd : ps.mapM bitDecode = some i) (hw : WellFormed i) :
    ∃ bs : List Bits, flatten count ((ps.map delimit).flatten) = (bs.map delimit).flatten ∧
      bs.map decodeNat = expand count i := by
  induction ps generalizing i with
  | nil =>
    have : i = [] := by simpa using hd.symm
    subst i
    exact ⟨[], rfl, rfl⟩
  | cons b ps ih =>
    rw [List.mapM_cons] at hd
    obtain ⟨p, hp, hs⟩ := Option.bind_eq_some_iff.mp hd
    obtain ⟨i', hi', he⟩ := Option.bind_eq_some_iff.mp hs
    have hi : p :: i' = i := Option.some.inj he
    subst i
    obtain ⟨a, r, rfl, ha, hr⟩ := decoded_pair_parts hp
    change some (decodeNat a) = _ at ha
    change some (decodeNat r) = _ at hr
    have hp' : (decodeNat a, decodeNat r) = p := Prod.ext (Option.some.inj ha) (Option.some.inj hr)
    subst p
    have hpos := hw _ (List.mem_cons_self ..)
    obtain ⟨bs, he, hs⟩ := ih hi' (fun p hp => hw p (List.mem_cons_of_mem _ hp))
    refine ⟨(if count then [[true], [true]] else [a, r]) ++ bs, ?_, ?_⟩
    · simp only [List.map_cons, List.flatten_cons, flatten_pair count
        ((decodeNat_pos a).mp hpos.1) ((decodeNat_pos r).mp hpos.2), he]
      cases count <;> simp [List.append_assoc]
    · cases count <;> simp [expand, hs, show decodeNat [true] = 1 by rfl]

private theorem decode_flatten (count : Bool) {x : Bits} {i : PairedPartitionInstance}
    (hd : bitDecode x = some i) (hw : WellFormed i) :
    bitDecode (α := List ℕ) (flatten count x) = some (expand count i) := by
  change (undelimitBlocks x).bind (List.mapM bitDecode) = _ at hd
  obtain ⟨ps, hp, hi⟩ := Option.bind_eq_some_iff.mp hd
  obtain ⟨bs, he, hs⟩ := flatten_spec count ps hi hw
  rw [blocks_decode_sound hp, he, decode_list_nat, undelimitBlocks_flatten_delimit, Option.map_some,
    hs]

/-! ### The Boolean choice verifier -/

private def mask : Bits → Bits :=
  scan (fun (_ : Unit) b => ((), [b, !b])) (fun _ => []) ()

private def ssInput (count : Bool) (x : Bits) : Bits :=
  Partition.reduceToSubsetSum (flatten count x)

private def verify (q : Bits × Bits) : Bool :=
  (valid q.1 && SSVerify.ssCheck (ssInput true q.1) (mask q.2)) &&
    SSVerify.ssCheck (ssInput false q.1) (mask q.2)

private theorem polyVerify : IsPolyTime verify := by
  let x (u : Bits) := unframe (field true u)
  let w (u : Bits) := unframe (field false u)
  have hx : IsPolyTime x := (polyScan ..).comp (polyScan ..)
  have hw : IsPolyTime w := (polyScan ..).comp (polyScan ..)
  have hhead : IsPolyTime (fun x : Bits => x.headD false) :=
    isPolyTime_dup.comp (isPolyTime_heads fun a _ => a)
  have hv : IsPolyTime valid := (polyScan ..).comp hhead
  have hcheck (count : Bool) : IsPolyTime
      (fun u => SSVerify.ssCheck (ssInput count (x u)) (mask (w u))) := by
    have hflat : IsPolyTime (flatten count) := polyScan ..
    have hf : IsPolyTime (ssInput count) :=
      hflat.comp Partition.MembershipMachine.isPolyTime_reduceToSubsetSum
    exact (polyPair (hx.comp hf) (hw.comp (polyScan ..))).comp isPolyTime_ssCheck
  apply polyEncoded (((hx.comp hv).combine Bool.and (hcheck true)).combine Bool.and (hcheck false))
  rintro ⟨a, b⟩
  change verify (x (delimit (bitEncode a) ++ bitEncode b), w (delimit (bitEncode a) ++ bitEncode b))
    = verify (a, b)
  simp [x, w, field_delimit, unframe_encode]

private def selected (count : Bool) (p : ℕ × ℕ) (b : Bool) : ℕ :=
  if count then 1 else chosen p b

private theorem mask_cons (b : Bool) (w : Bits) : mask (b :: w) = b :: (!b) :: mask w := rfl

private theorem pick_expand (count : Bool) (i : PairedPartitionInstance) (w : Bits) :
    SSVerify.pick ((expand count i).map (· * 2)) (mask w) =
      (List.zipWith (selected count) i w).map (· * 2) := by
  induction i generalizing w with
  | nil => rfl
  | cons p i ih =>
    rw [expand_cons]
    cases w with
    | nil =>
      have h := ih []
      simp only [List.zipWith_nil_right, List.map_nil, show mask [] = [] from rfl] at h
      cases count <;> simpa [SSVerify.pick, show mask [] = [] from rfl] using h
    | cons b w =>
      rw [mask_cons]
      cases count <;> cases b <;>
        simp [selected, chosen, SSVerify.pick, ih w]

private theorem sum_expand (count : Bool) (i : PairedPartitionInstance) :
    (expand count i).sum = if count then 2 * i.length else (i.map fun p => p.1 + p.2).sum := by
  induction i with
  | nil => cases count <;> rfl
  | cons p i ih =>
    rw [expand_cons, List.sum_append, ih]
    cases count <;> simp only [↓reduceIte, Bool.false_eq_true, List.map_cons, List.sum_cons,
      List.sum_nil, List.length_cons] <;> omega

private theorem sum_units (i : PairedPartitionInstance) (w : Bits) :
    (List.zipWith (selected true) i w).sum = min i.length w.length := by
  induction i generalizing w with
  | nil => simp
  | cons p i ih =>
    cases w with
    | nil => simp
    | cons b w =>
      simp only [List.zipWith_cons_cons, List.sum_cons, selected, ↓reduceIte, ih, List.length_cons]
      omega

private theorem zip_take (i : PairedPartitionInstance) (w : Bits) :
    List.zipWith chosen i (w.take i.length) = List.zipWith chosen i w := by
  induction i generalizing w with
  | nil => rfl
  | cons p i ih => cases w <;> simp [ih]

private theorem ssInput_spec (count : Bool) {x : Bits} {i : PairedPartitionInstance}
    (hd : bitDecode x = some i) (hw : WellFormed i) (w : Bits) :
    SSVerify.ssCheck (ssInput count x) (mask w) = true ↔
      (List.zipWith (selected count) i w).sum * 2 = (expand count i).sum := by
  simp only [ssInput, Partition.reduceToSubsetSum, decode_flatten count hd hw, SSVerify.ssCheck,
    SSVerify.decodeSS_eq_some.mpr rfl, beq_iff_eq, pick_expand]
  have hsum := List.sum_map_mul_right (List.zipWith (selected count) i w) id (2 : ℕ)
  simp only [id_eq, List.map_id] at hsum
  rw [hsum]

private theorem valid_iff {x : Bits} {i : PairedPartitionInstance} (hd : bitDecode x = some i) :
    valid x = true ↔ WellFormed i := by
  rw [valid_eq, hd]
  simp [WellFormed, List.all_eq_true]

private theorem membership : pairedPartitionDec ∈ NP := by
  classical
  refine ⟨Polynomial.X, verify, polyVerify, fun x => ?_⟩
  cases hd : bitDecode (α := PairedPartitionInstance) x with
  | none => simp [pairedPartitionDec, verify, valid_eq, hd]
  | some i =>
    simp only [pairedPartitionDec, hd, decide_eq_true_eq, Polynomial.eval_X]
    by_cases hw : WellFormed i
    · have hv := (valid_iff hd).2 hw
      have hc (w : Bits) : SSVerify.ssCheck (ssInput true x) (mask w) = true ↔
          i.length ≤ w.length := by
        rw [ssInput_spec _ hd hw, sum_expand, sum_units]
        simp only [↓reduceIte]
        omega
      have hs (w : Bits) : SSVerify.ssCheck (ssInput false x) (mask w) = true ↔
          (List.zipWith chosen i w).sum * 2 = (i.map fun p => p.1 + p.2).sum := by
        have he := ssInput_spec false hd hw w
        rw [sum_expand] at he
        exact he
      simp only [hw, true_and, verify, hv, Bool.true_and, Bool.and_eq_true, hc, hs]
      constructor
      · rintro ⟨w, hlen, he⟩
        exact ⟨w, hlen ▸ decoded_list_length_le hd, hlen.ge, he⟩
      · rintro ⟨w, _, hlen, he⟩
        exact ⟨w.take i.length, by simp [hlen], by simpa [zip_take] using he⟩
    · have hv : valid x = false := Bool.eq_false_iff.mpr fun h => hw ((valid_iff hd).1 h)
      simp [hw, verify, hv]

/-- **PARTITION choosing one element of each pair is NP-complete.**
Source: Garey and Johnson (1979), [SP12], comment. -/
public theorem pairedPartition_npComplete :
    pairedPartitionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L pairedPartitionDec :=
  ⟨membership, Cslib.Complexity.NPHard.of_polyManyOneRed Partition.partition_npComplete.2
    ⟨reduce, polyReduce, reduce_correct⟩⟩

end MetaMathlibExt.Complexity.NPComplete.PairedPartition
