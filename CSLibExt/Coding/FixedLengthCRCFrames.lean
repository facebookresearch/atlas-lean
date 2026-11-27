/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Coding.UnreflectedSerialCRC
public import CSLibExt.Computability.Automata.Transducers.Sequential
public import MathlibExt.Data.BitEncoding
public import MathlibExt.Data.BitVec.BinaryPolynomialArithmetic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Fintype.EquivFin

/-!
# Fixed-length CRC-protected framed parser

Tokens are `start`, `bit b` for a body bit `b`, and `endTok`. A frame is
one `start`, then exactly `l + r` body bits, then one `endTok`. The body
is an `l`-bit MSB-first payload followed by the `r`-bit check register
of the zero-init unreflected serial CRC of the payload, sent MSB first.
The parser is a sequential transducer: bits before any `start` or after
a failure are rejected, a `start` in any phase aborts the current frame
and restarts from the fresh state `freshState` (`frame_step_start`,
`run_start_cons`), and on `endTok` the parser accepts exactly when the
body length is `l + r` and the serial CRC register run over the whole
body is the zero register (`runState_freshState_frame`). While reading,
the parser emits the first `l` body bits, so an accepted single frame
returns its payload, leading zeros included, at its declared length `l`.

Bits are emitted before a frame is validated. A token list is accepted
exactly when its final frame is (`translates_iff_zero_remainder_body`):
an earlier frame that is rejected, or cut short by the next `start`, is
discarded at that `start`, does not make the stream rejected, and the
bits it emitted stay in the accepted output. So the output of an
accepted stream is the sequence of its payloads only when every frame
in it is clean (`twoConsecutiveFrames_translate`).

The parser state is a phase, the CRC register, and a count of body bits
read that saturates at `l + r + 1`, so the state space is finite and a
bit step updates a bounded counter instead of an accumulated body.
-/

@[expose] public section

namespace CSLibExt.Coding.FixedLengthCRCFrames

open CSLibExt.Coding.UnreflectedSerialCRC
open Cslib.Automata

/-- A framing token: frame start, one body bit, or frame end. -/
inductive FrameToken where
  | start : FrameToken
  | bit : Bool → FrameToken
  | endTok : FrameToken
deriving DecidableEq

/-- The parser phase: waiting for a start, inside a body, accepted, or
failed. -/
inductive ParserPhase where
  | awaitingStart : ParserPhase
  | inBody : ParserPhase
  | done : ParserPhase
  | failed : ParserPhase
deriving DecidableEq

/-- There are four parser phases. -/
instance instFiniteParserPhase : Finite ParserPhase :=
  Finite.of_injective
    (fun p : ParserPhase => match p with
      | .awaitingStart => (0 : Fin 4)
      | .inBody => 1
      | .done => 2
      | .failed => 3)
    (by
      intro a b h
      cases a <;> cases b <;> first | rfl | exact absurd h (by decide))

/-- The saturating body-bit count: `n` capped at `l + r + 1`, the first
value above the accepted body length `l + r`. -/
def satCount (l r n : ℕ) : Fin (l + r + 2) :=
  ⟨min n (l + r + 1), by omega⟩

/-- The parser state: phase, serial CRC register over the body so far,
and the number of body bits received in the current frame, saturating
at `l + r + 1`. -/
structure ParserState (l r : ℕ) where
  phase : ParserPhase
  register : BitVec r
  count : Fin (l + r + 2)

/-- The parser state space is finite. -/
instance instFiniteParserState (l r : ℕ) : Finite (ParserState l r) :=
  Finite.of_injective (fun q : ParserState l r => (q.phase, q.register.toFin, q.count))
    (by
      rintro ⟨p₁, g₁, c₁⟩ ⟨p₂, g₂, c₂⟩ h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, hg, rfl⟩ := h
      rw [BitVec.eq_of_toFin_eq hg])

/-- The fresh candidate-frame state entered on every `start`: inside a body, zero
register, zero body bits counted. -/
def freshState (l r : ℕ) : ParserState l r :=
  { phase := ParserPhase.inBody, register := 0#r, count := satCount l r 0 }

/-- The fixed-length framed parser as a sequential transducer. A
`start` token in any phase aborts the current frame and restarts from
`freshState`. Inside a body, each bit updates the serial CRC register and
the saturating count, and is emitted while fewer than `l` bits have
been received. On `endTok` the parser accepts exactly when the count
is `l + r` and the register is zero. Any other token fails the
frame. -/
def frameParser (l r : ℕ) (taps : BitVec r) :
    Cslib.Automata.SequentialTransducer (ParserState l r) FrameToken Bool where
  step := fun q tok =>
    match q.phase, tok with
    | _, FrameToken.start => (freshState l r, [])
    | ParserPhase.inBody, FrameToken.bit b =>
        ({ phase := ParserPhase.inBody,
           register := stepRegister r taps q.register b,
           count := satCount l r (q.count.val + 1) },
         if q.count.val < l then [b] else [])
    | ParserPhase.inBody, FrameToken.endTok =>
        ({ phase := if q.count.val = l + r ∧ q.register = 0#r then
              ParserPhase.done else ParserPhase.failed,
           register := q.register, count := q.count }, [])
    | _, _ =>
        ({ phase := ParserPhase.failed, register := q.register,
           count := q.count }, [])
  start := { phase := ParserPhase.awaitingStart, register := 0#r, count := satCount l r 0 }
  accept := { q | q.phase = ParserPhase.done }
  initOut := []
  finalOut := fun _ => []

/-- The transmitted check bits: the final register, MSB first. -/
def checkBits (r : ℕ) (taps : BitVec r) (bits : List Bool) : List Bool :=
  Nat.toBitsBE r (finalRegister r taps bits).toNat

/-- The frame body: payload followed by its check bits. -/
def encodedBody (r : ℕ) (taps : BitVec r) (bits : List Bool) : List Bool :=
  bits ++ checkBits r taps bits

/-- The encoded frame tokens for a payload. -/
def encodeFrame (r : ℕ) (taps : BitVec r) (bits : List Bool) :
    List FrameToken :=
  FrameToken.start :: (encodedBody r taps bits).map FrameToken.bit ++
    [FrameToken.endTok]

/-! ### Helper lemmas -/

/-- The saturating count is `min n (l + r + 1)`. -/
theorem satCount_val (l r n : ℕ) : (satCount l r n).val = min n (l + r + 1) :=
  rfl

private theorem satCount_zero_val (l r : ℕ) : (satCount l r 0).val = 0 := by
  rw [satCount_val]
  omega

/-- Adding `m` to a saturated count and saturating again gives the saturated count of
`n + m`. -/
theorem satCount_add (l r n m : ℕ) :
    satCount l r ((satCount l r n).val + m) = satCount l r (n + m) := by
  apply Fin.ext
  simp only [satCount_val]
  omega

private theorem satCount_self (l r : ℕ) (c : Fin (l + r + 2)) : satCount l r c.val = c := by
  apply Fin.ext
  have hc := c.isLt
  rw [satCount_val]
  omega

/-- The saturating count equals the frame length `l + r` exactly when the plain count does. -/
theorem satCount_val_eq_iff (l r n : ℕ) :
    (satCount l r n).val = l + r ↔ n = l + r := by
  rw [satCount_val]
  constructor <;> intro h <;> omega

/-- **Reset rule, one step.** From every state, `start` moves to the fresh candidate state
`freshState` and emits nothing. -/
theorem frame_step_start (l r : ℕ) (taps : BitVec r) (q : ParserState l r) :
    (frameParser l r taps).step q FrameToken.start = (freshState l r, []) := by
  cases q with
  | mk phase reg cnt =>
      cases phase <;> rfl

/-- **Reset rule, runs.** After `start`, the run from any state coincides, in final state and
in output, with the run from the fresh candidate state: the unfinished frame's register,
count and phase are discarded. -/
theorem run_start_cons (l r : ℕ) (taps : BitVec r) (q : ParserState l r)
    (ts : List FrameToken) :
    (frameParser l r taps).runState q (FrameToken.start :: ts) =
        (frameParser l r taps).runState (freshState l r) ts ∧
      (frameParser l r taps).runOut q (FrameToken.start :: ts) =
        (frameParser l r taps).runOut (freshState l r) ts := by
  constructor
  · rw [SequentialTransducer.runState_cons, frame_step_start]
  · simp only [SequentialTransducer.runOut_cons, frame_step_start,
      List.nil_append]

/-- Inside a body, a bit steps the serial register, advances the saturating count, and is
emitted while fewer than `l` bits have been read. -/
theorem frame_step_bit_inBody (l r : ℕ) (taps : BitVec r)
    (reg : BitVec r) (c : Fin (l + r + 2)) (b : Bool) :
    (frameParser l r taps).step
        { phase := ParserPhase.inBody, register := reg, count := c }
        (FrameToken.bit b) =
      ({ phase := ParserPhase.inBody,
         register := stepRegister r taps reg b,
         count := satCount l r (c.val + 1) },
       if c.val < l then [b] else []) := rfl

private theorem frame_step_end_inBody (l r : ℕ) (taps : BitVec r)
    (reg : BitVec r) (c : Fin (l + r + 2)) :
    (frameParser l r taps).step
        { phase := ParserPhase.inBody, register := reg, count := c }
        FrameToken.endTok =
      ({ phase := if c.val = l + r ∧ reg = (0#r : BitVec r) then
            ParserPhase.done else ParserPhase.failed,
         register := reg, count := c }, []) := rfl

private theorem checkBits_length (r : ℕ) (taps : BitVec r) (bits : List Bool) :
    (checkBits r taps bits).length = r := by
  simp [checkBits, Nat.length_toBitsBE]

private theorem encodedBody_length (r : ℕ) (taps : BitVec r) (bits : List Bool) :
    (encodedBody r taps bits).length = bits.length + r := by
  simp [encodedBody, checkBits_length]

private theorem encodedBody_take (l r : ℕ) (taps : BitVec r) (bits : List Bool)
    (hlen : bits.length = l) :
    (encodedBody r taps bits).take l = bits := by
  unfold encodedBody
  exact List.take_left' hlen

private theorem runRegister_eq_runState_zero (r : ℕ) (taps : BitVec r)
    (bits : List Bool) :
    runRegister r taps bits = (serialLFSR r taps).runState (0#r : BitVec r) bits :=
  rfl

private theorem serial_step_fst (r : ℕ) (taps : BitVec r) (w : BitVec r)
    (b : Bool) :
    ((serialLFSR r taps).step w b).1 = stepRegister r taps w b := rfl

/-- Reading body bits inside a body runs the serial register over them and adds their
number to the saturating count. -/
theorem run_bits_inBody_state (l r : ℕ) (taps : BitVec r)
    (reg : BitVec r) (c : Fin (l + r + 2)) (body : List Bool) :
    (frameParser l r taps).runState
        { phase := ParserPhase.inBody, register := reg, count := c }
        (body.map FrameToken.bit) =
      { phase := ParserPhase.inBody,
        register := (serialLFSR r taps).runState reg body,
        count := satCount l r (c.val + body.length) } := by
  induction body generalizing reg c with
  | nil =>
      change ({ phase := ParserPhase.inBody, register := reg, count := c } : ParserState l r) =
        { phase := ParserPhase.inBody, register := reg, count := satCount l r (c.val + 0) }
      rw [Nat.add_zero, satCount_self]
  | cons b bs ih =>
      simp only [List.map_cons]
      rw [SequentialTransducer.runState_cons]
      simp only [frame_step_bit_inBody]
      rw [ih]
      have hMealy : (serialLFSR r taps).runState reg (b :: bs) =
          (serialLFSR r taps).runState (stepRegister r taps reg b) bs := by
        have h := MealyMachine.runState_cons (serialLFSR r taps) reg b bs
        simp only [serial_step_fst] at h
        exact h
      have hLen : c.val + 1 + bs.length = c.val + (b :: bs).length := by
        simp only [List.length_cons]
        omega
      rw [hMealy, satCount_add, hLen]

/-- Reading body bits inside a body emits those of them that fall among the first `l`. -/
theorem run_bits_inBody_out (l r : ℕ) (taps : BitVec r)
    (reg : BitVec r) (c : Fin (l + r + 2)) (body : List Bool) :
    (frameParser l r taps).runOut
        { phase := ParserPhase.inBody, register := reg, count := c }
        (body.map FrameToken.bit) =
      body.take (l - c.val) := by
  induction body generalizing reg c with
  | nil => simp [SequentialTransducer.runOut_nil]
  | cons b bs ih =>
      simp only [List.map_cons]
      rw [SequentialTransducer.runOut_cons]
      simp only [frame_step_bit_inBody]
      rw [ih, satCount_val]
      by_cases h : c.val < l
      · simp only [ite_eq_left h]
        have hSub : l - c.val = (l - min (c.val + 1) (l + r + 1)) + 1 := by omega
        rw [hSub]
        simp
      · simp only [ite_eq_right h]
        have hSub0 : l - c.val = 0 := by omega
        have hSub1 : l - min (c.val + 1) (l + r + 1) = 0 := by omega
        rw [hSub0, hSub1]
        simp

/-- **End-of-frame decision.** A candidate frame read from the fresh state and closed by
`endTok` is accepted exactly when its body has `l + r` bits and zero CRC register, and fails
otherwise; the register and the saturating count are those of the body. -/
theorem runState_freshState_frame (l r : ℕ) (taps : BitVec r)
    (body : List Bool) :
    (frameParser l r taps).runState (freshState l r)
        (body.map FrameToken.bit ++ [FrameToken.endTok]) =
      { phase :=
          if body.length = l + r ∧ runRegister r taps body = (0#r : BitVec r) then
            ParserPhase.done else ParserPhase.failed,
        register := runRegister r taps body,
        count := satCount l r body.length } := by
  rw [freshState, SequentialTransducer.runState_append, run_bits_inBody_state, satCount_add,
    Nat.zero_add, ← runRegister_eq_runState_zero, SequentialTransducer.runState_cons]
  simp [frame_step_end_inBody, SequentialTransducer.runState_nil, satCount_val_eq_iff]

private theorem fresh_rest_runOut (l r : ℕ) (taps : BitVec r)
    (body : List Bool) :
    (frameParser l r taps).runOut (freshState l r)
        (body.map FrameToken.bit ++ [FrameToken.endTok]) =
      body.take l := by
  rw [freshState, SequentialTransducer.runOut_append, run_bits_inBody_out, run_bits_inBody_state,
    SequentialTransducer.runOut_cons]
  simp [frame_step_end_inBody, SequentialTransducer.runOut_nil, satCount_zero_val]

private theorem single_frame_runState (l r : ℕ) (taps : BitVec r)
    (body : List Bool) :
    (frameParser l r taps).runState (frameParser l r taps).start
      (FrameToken.start :: body.map FrameToken.bit ++ [FrameToken.endTok]) =
      { phase :=
          if body.length = l + r ∧ runRegister r taps body = (0#r : BitVec r) then
            ParserPhase.done else ParserPhase.failed,
        register := runRegister r taps body,
        count := satCount l r body.length } := by
  rw [List.cons_append, SequentialTransducer.runState_cons, frame_step_start]
  exact runState_freshState_frame l r taps body

private theorem single_frame_runOut (l r : ℕ) (taps : BitVec r)
    (body : List Bool) :
    (frameParser l r taps).runOut (frameParser l r taps).start
      (FrameToken.start :: body.map FrameToken.bit ++ [FrameToken.endTok]) =
      body.take l := by
  rw [List.cons_append, SequentialTransducer.runOut_cons, frame_step_start]
  simp only [List.nil_append]
  exact fresh_rest_runOut l r taps body

private theorem frameParser_initOut (l r : ℕ) (taps : BitVec r) :
    (frameParser l r taps).initOut = [] := rfl

private theorem frameParser_finalOut_apply (l r : ℕ) (taps : BitVec r)
    (q : ParserState l r) :
    (frameParser l r taps).finalOut q = [] := rfl

private theorem frameParser_accept_iff (l r : ℕ) (taps : BitVec r)
    (q : ParserState l r) :
    q ∈ (frameParser l r taps).accept ↔ q.phase = ParserPhase.done := Iff.rfl

private theorem frame_translates_single (l r : ℕ) (taps : BitVec r)
    (body : List Bool) (out : List Bool) :
    (frameParser l r taps).Translates
        (FrameToken.start :: body.map FrameToken.bit ++ [FrameToken.endTok])
        out ↔
      (body.length = l + r ∧ runRegister r taps body = (0#r : BitVec r)) ∧
        out = body.take l := by
  simp only [Cslib.Automata.SequentialTransducer.Translates, frameParser_initOut,
    frameParser_finalOut_apply, List.nil_append, List.append_nil]
  rw [single_frame_runState, single_frame_runOut]
  simp only [frameParser_accept_iff]
  constructor
  · intro h
    obtain ⟨hPhase, hOut⟩ := h
    have hCond : body.length = l + r ∧ runRegister r taps body = (0#r : BitVec r) := by
      by_contra hCon
      simp only [ite_eq_right hCon] at hPhase
      exact ParserPhase.noConfusion hPhase
    exact ⟨hCond, hOut.symm⟩
  · intro h
    obtain ⟨hCond, hOut⟩ := h
    simp only [ite_eq_left hCond, hOut, and_true]

private theorem two_frame_translates_aux (l r : ℕ) (taps : BitVec r)
    (b₁ b₂ : List Bool)
    (h₁len : b₁.length = l + r)
    (h₁reg : runRegister r taps b₁ = (0#r : BitVec r))
    (h₂len : b₂.length = l + r)
    (h₂reg : runRegister r taps b₂ = (0#r : BitVec r)) :
    (frameParser l r taps).Translates
      ((FrameToken.start :: b₁.map FrameToken.bit ++ [FrameToken.endTok]) ++
        (FrameToken.start :: b₂.map FrameToken.bit ++ [FrameToken.endTok]))
      (b₁.take l ++ b₂.take l) := by
  simp only [Cslib.Automata.SequentialTransducer.Translates, frameParser_initOut,
    frameParser_finalOut_apply, List.nil_append, List.append_nil]
  constructor
  · rw [SequentialTransducer.runState_append]
    have hS1 := single_frame_runState l r taps b₁
    rw [ite_eq_left ⟨h₁len, h₁reg⟩] at hS1
    rw [hS1]
    rw [List.cons_append]
    rw [(run_start_cons l r taps _ _).1]
    rw [runState_freshState_frame]
    simp only [frameParser_accept_iff]
    rw [ite_eq_left ⟨h₂len, h₂reg⟩]
  · rw [SequentialTransducer.runOut_append]
    have hO1 := single_frame_runOut l r taps b₁
    rw [hO1]
    have hS1 := single_frame_runState l r taps b₁
    rw [hS1]
    rw [List.cons_append]
    rw [(run_start_cons l r taps _ _).2]
    rw [fresh_rest_runOut]

private theorem mulXMod_xor (r : ℕ) (taps a b : BitVec r) :
    taps.mulXMod (a ^^^ b) = taps.mulXMod a ^^^ taps.mulXMod b := by
  unfold BitVec.mulXMod
  have hshift : ∀ x y : BitVec r, (x ^^^ y) <<< 1 = (x <<< 1) ^^^ (y <<< 1) := by
    intro x y
    ext i
    by_cases h : i = 0 <;> simp [h]
  by_cases ha : a.getMsbD 0 <;> by_cases hb : b.getMsbD 0 <;>
    simp only [ha, hb, BitVec.getMsbD_xor, Bool.xor_true, Bool.xor_false, ite_true] <;> grind

private theorem mulXMod_zero (r : ℕ) (taps : BitVec r) :
    taps.mulXMod (0#r : BitVec r) = 0#r := by
  simp [BitVec.mulXMod]

private def mulXModPow (r : ℕ) (taps : BitVec r) : ℕ → BitVec r → BitVec r
  | 0, w => w
  | n + 1, w => mulXModPow r taps n (taps.mulXMod w)

private theorem mulXModPow_zero (r : ℕ) (taps : BitVec r) (w : BitVec r) :
    mulXModPow r taps 0 w = w := rfl

private theorem mulXModPow_succ (r : ℕ) (taps : BitVec r) (n : ℕ) (w : BitVec r) :
    mulXModPow r taps (n + 1) w = mulXModPow r taps n (taps.mulXMod w) := rfl

private theorem mulXModPow_xor (r : ℕ) (taps : BitVec r) (n : ℕ) (a b : BitVec r) :
    mulXModPow r taps n (a ^^^ b) =
      mulXModPow r taps n a ^^^ mulXModPow r taps n b := by
  induction n generalizing a b with
  | zero => simp [mulXModPow_zero]
  | succ n ih =>
      rw [mulXModPow_succ, mulXModPow_succ, mulXModPow_succ, mulXMod_xor, ih]

private theorem stepRegister_zero (r : ℕ) (taps : BitVec r) (b : Bool) :
    stepRegister r taps (0#r : BitVec r) b = inputBit r b := by
  simp [stepRegister, mulXMod_zero]

private theorem runState_serial_decomp (r : ℕ) (taps : BitVec r)
    (bits : List Bool) (x : BitVec r) :
    (serialLFSR r taps).runState x bits =
      (serialLFSR r taps).runState (0#r : BitVec r) bits ^^^
        mulXModPow r taps bits.length x := by
  induction bits generalizing x with
  | nil =>
      change x = (0#r : BitVec r) ^^^ x
      simp
  | cons b bs ih =>
      have hstep : ∀ y : BitVec r,
          (serialLFSR r taps).runState y (b :: bs) =
            (serialLFSR r taps).runState (stepRegister r taps y b) bs := by
        intro y
        have h := MealyMachine.runState_cons (serialLFSR r taps) y b bs
        simpa only [serial_step_fst] using h
      rw [hstep x, hstep (0#r : BitVec r), ih, ih (stepRegister r taps (0#r : BitVec r) b)]
      rw [stepRegister_zero]
      have hlen : (b :: bs).length = bs.length + 1 := rfl
      rw [hlen, mulXModPow_succ]
      simp only [stepRegister]
      rw [mulXModPow_xor]
      grind

private theorem runState_serial_zeros (r : ℕ) (taps : BitVec r) (n : ℕ)
    (x : BitVec r) :
    (serialLFSR r taps).runState x (List.replicate n false) =
      mulXModPow r taps n x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      rw [List.replicate_succ]
      have h := MealyMachine.runState_cons (serialLFSR r taps) x false
        (List.replicate n false)
      rw [show (serialLFSR r taps).runState x (false :: List.replicate n false) =
          (serialLFSR r taps).runState (stepRegister r taps x false)
            (List.replicate n false) by simpa only [serial_step_fst] using h]
      rw [ih]
      have hstep : stepRegister r taps x false = taps.mulXMod x := by
        simp [stepRegister, inputBit]
      rw [hstep, mulXModPow_succ]

private theorem ofBitsBE_cons (a : Bool) (as : List Bool) :
    Nat.ofBitsBE (a :: as) = (if a then 2 ^ as.length else 0) + Nat.ofBitsBE as := by
  simp only [Nat.ofBitsBE, BitVec.ofBoolListBE, BitVec.toNat_cons]
  rw [← Nat.shiftLeft_add_eq_or_of_lt (BitVec.isLt _)]
  cases a <;> simp [Nat.shiftLeft_eq]

private theorem stepRegister_ofNat (r : ℕ) (taps : BitVec r) (a k : ℕ)
    (ha : a < 2 ^ k) (hk : k < r) (b : Bool) :
    stepRegister r taps (BitVec.ofNat r a) b =
      BitVec.ofNat r (2 * a + (if b then 1 else 0)) := by
  apply BitVec.eq_of_toNat_eq
  have hk1 : k ≤ r - 1 := by omega
  have ha1 : a < 2 ^ (r - 1) :=
    lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) hk1)
  have hmsb : (BitVec.ofNat r a).getMsbD 0 = false := by
    rw [BitVec.getMsbD_eq_getLsbD]
    simp [BitVec.getLsbD_ofNat, Nat.testBit_lt_two_pow ha1]
  have haR : a < 2 ^ r :=
    lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) (le_of_lt hk))
  have h2a : 2 * a + (if b then 1 else 0) < 2 ^ r := by
    have hpow : (2 : ℕ) ^ r = 2 * 2 ^ (r - 1) := by
      conv_lhs => rw [show r = (r - 1) + 1 by omega]
      rw [pow_succ]
      ring
    cases b <;> simp at * <;> omega
  have h2abound : 2 * a < 2 ^ r := by
    have hpow : (2 : ℕ) ^ r = 2 * 2 ^ (r - 1) := by
      conv_lhs => rw [show r = (r - 1) + 1 by omega]
      rw [pow_succ]
      ring
    omega
  rw [stepRegister, BitVec.toNat_xor]
  have hmul : taps.mulXMod (BitVec.ofNat r a) = (BitVec.ofNat r a) <<< 1 := by
    simp [BitVec.mulXMod, hmsb]
  rw [hmul, BitVec.toNat_shiftLeft]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt haR, Nat.mod_eq_of_lt h2a]
  have hshift : (a <<< 1) % 2 ^ r = 2 * a := by
    rw [Nat.shiftLeft_eq]
    simp only [pow_one]
    rw [Nat.mod_eq_of_lt (show a * 2 < 2 ^ r by omega)]
    ring
  rw [hshift]
  cases b with
  | false => simp [inputBit]
  | true =>
      have h1 : ((1#r : BitVec r)).toNat = 1 := by
        have hlt : (1 : ℕ) < 2 ^ r := Nat.one_lt_two_pow_iff.mpr (by omega)
        simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
      simp only [inputBit, ite_true, h1]
      exact Nat.xor_one_of_even ⟨a, by ring⟩

private theorem runState_ofNat (r : ℕ) (taps : BitVec r) (bits : List Bool)
    (a k : ℕ) (ha : a < 2 ^ k) (hk : k + bits.length ≤ r) :
    (serialLFSR r taps).runState (BitVec.ofNat r a) bits =
      BitVec.ofNat r (a * 2 ^ bits.length + Nat.ofBitsBE bits) := by
  induction bits generalizing a k with
  | nil =>
      change BitVec.ofNat r a = BitVec.ofNat r (a * 2 ^ 0 + Nat.ofBitsBE [])
      simp [Nat.ofBitsBE, BitVec.ofBoolListBE]
  | cons b bs ih =>
      simp only [List.length_cons] at hk
      have hb : 2 * a + (if b then 1 else 0) < 2 ^ (k + 1) := by
        rw [pow_succ]
        cases b <;> simp <;> omega
      rw [MealyMachine.runState_cons, serial_step_fst,
        stepRegister_ofNat r taps a k ha (by omega) b,
        ih (2 * a + (if b then 1 else 0)) (k + 1) hb (by omega), ofBitsBE_cons]
      congr 1
      cases b <;> simp [List.length_cons, pow_succ] <;> ring

private theorem runState_zero_toBitsBE (r : ℕ) (taps : BitVec r) (v : BitVec r) :
    (serialLFSR r taps).runState (0#r : BitVec r) (Nat.toBitsBE r v.toNat) = v := by
  rw [runState_ofNat r taps _ 0 0 (by norm_num) (by simp), Nat.ofBitsBE_toBitsBE,
    Nat.mod_eq_of_lt v.isLt]
  apply BitVec.eq_of_toNat_eq
  simp

private theorem finalRegister_eq_pow (r : ℕ) (taps : BitVec r) (bits : List Bool) :
    finalRegister r taps bits =
      mulXModPow r taps r (runRegister r taps bits) := by
  unfold finalRegister runRegister
  rw [← MealyMachine.seq_runState_eq _ (bits ++ List.replicate r false),
    SequentialTransducer.runState_append]
  simp only [MealyMachine.seq_runState_eq]
  exact runState_serial_zeros r taps r _


private theorem runOut_inBody_bits_end (l r : ℕ) (taps : BitVec r)
    (reg : BitVec r) (c : Fin (l + r + 2)) (suffix : List Bool) :
    (frameParser l r taps).runOut
        { phase := ParserPhase.inBody, register := reg, count := c }
        (suffix.map FrameToken.bit ++ [FrameToken.endTok]) =
      suffix.take (l - c.val) := by
  rw [SequentialTransducer.runOut_append, run_bits_inBody_out, run_bits_inBody_state,
    SequentialTransducer.runOut_cons]
  simp [frame_step_end_inBody, SequentialTransducer.runOut_nil]

private theorem prefix_frame_translates (l r : ℕ) (taps : BitVec r)
    (pfx : List FrameToken) (body : List Bool)
    (hLen : body.length = l + r) (hReg : runRegister r taps body = 0#r) :
    (frameParser l r taps).Translates
      (pfx ++ (FrameToken.start :: body.map FrameToken.bit ++ [FrameToken.endTok]))
      ((frameParser l r taps).runOut (frameParser l r taps).start pfx ++
        body.take l) := by
  simp only [Cslib.Automata.SequentialTransducer.Translates, frameParser_initOut,
    frameParser_finalOut_apply, List.nil_append, List.append_nil]
  constructor
  · rw [SequentialTransducer.runState_append, List.cons_append, (run_start_cons l r taps _ _).1,
      runState_freshState_frame]
    simp only [frameParser_accept_iff]
    rw [ite_eq_left ⟨hLen, hReg⟩]
  · rw [SequentialTransducer.runOut_append, List.cons_append, (run_start_cons l r taps _ _).2,
      fresh_rest_runOut]

private theorem start_prefix_runOut (l r : ℕ) (taps : BitVec r)
    (prefixBits : List Bool) :
    (frameParser l r taps).runOut (frameParser l r taps).start
        (FrameToken.start :: prefixBits.map FrameToken.bit) =
      prefixBits.take l := by
  rw [SequentialTransducer.runOut_cons, frame_step_start]
  simp only [List.nil_append]
  rw [freshState, run_bits_inBody_out, satCount_zero_val, Nat.sub_zero]

private theorem step_phase_done (l r : ℕ) (taps : BitVec r) (q : ParserState l r)
    (a : FrameToken)
    (h : ((frameParser l r taps).step q a).1.phase = ParserPhase.done) :
    q.phase = ParserPhase.inBody ∧ a = FrameToken.endTok ∧
      q.count.val = l + r ∧ q.register = 0#r := by
  obtain ⟨qph, qreg, qcnt⟩ := q
  cases a with
  | start =>
      rw [frame_step_start] at h
      exact ParserPhase.noConfusion h
  | bit b => cases qph <;> exact ParserPhase.noConfusion h
  | endTok =>
      cases qph
      · exact ParserPhase.noConfusion h
      · by_cases hc : qcnt.val = l + r ∧ qreg = 0#r
        · exact ⟨rfl, rfl, hc.1, hc.2⟩
        · rw [frame_step_end_inBody, ite_eq_right hc] at h
          exact ParserPhase.noConfusion h
      · exact ParserPhase.noConfusion h
      · exact ParserPhase.noConfusion h

private theorem step_phase_inBody (l r : ℕ) (taps : BitVec r) (q : ParserState l r)
    (a : FrameToken)
    (h : ((frameParser l r taps).step q a).1.phase = ParserPhase.inBody) :
    a = FrameToken.start ∨
      (q.phase = ParserPhase.inBody ∧ ∃ b : Bool, a = FrameToken.bit b) := by
  obtain ⟨qph, qreg, qcnt⟩ := q
  cases a with
  | start => exact Or.inl rfl
  | bit b =>
      cases qph
      · exact ParserPhase.noConfusion h
      · exact Or.inr ⟨rfl, b, rfl⟩
      · exact ParserPhase.noConfusion h
      · exact ParserPhase.noConfusion h
  | endTok =>
      cases qph
      · exact ParserPhase.noConfusion h
      · rw [frame_step_end_inBody] at h
        by_cases hc : qcnt.val = l + r ∧ qreg = 0#r
        · rw [ite_eq_left hc] at h
          exact ParserPhase.noConfusion h
        · rw [ite_eq_right hc] at h
          exact ParserPhase.noConfusion h
      · exact ParserPhase.noConfusion h
      · exact ParserPhase.noConfusion h

private theorem accepted_cases (l r : ℕ) (taps : BitVec r) (q : ParserState l r)
    (ts : List FrameToken)
    (h : ((frameParser l r taps).runState q ts).phase = ParserPhase.done) :
    (ts = [] ∧ q.phase = ParserPhase.done) ∨
      (∃ pfx body, body.length = l + r ∧ runRegister r taps body = 0#r ∧
        ts = pfx ++
          (FrameToken.start :: body.map FrameToken.bit ++ [FrameToken.endTok]) ∧
        (frameParser l r taps).runOut q ts =
          (frameParser l r taps).runOut q pfx ++ body.take l) ∨
      (q.phase = ParserPhase.inBody ∧
        ∃ suffix, ts = suffix.map FrameToken.bit ++ [FrameToken.endTok] ∧
          q.count.val + suffix.length = l + r ∧
          (serialLFSR r taps).runState q.register suffix = 0#r ∧
          (frameParser l r taps).runOut q ts =
            suffix.take (l - q.count.val)) := by
  induction ts generalizing q with
  | nil =>
      exact Or.inl ⟨rfl, by simpa [SequentialTransducer.runState_nil] using h⟩
  | cons a ts ih =>
      have h' : ((frameParser l r taps).runState
          ((frameParser l r taps).step q a).1 ts).phase = ParserPhase.done := by
        rw [SequentialTransducer.runState_cons] at h
        exact h
      obtain (hA | hB | hC) := ih _ h'
      · obtain ⟨rfl, hphase⟩ := hA
        have hdone := step_phase_done l r taps q a hphase
        obtain ⟨hqph, rfl, hlen, hreg⟩ := hdone
        refine Or.inr (Or.inr ⟨hqph, [], rfl, ?_, ?_, ?_⟩)
        · simpa using hlen
        · exact hreg
        · rw [SequentialTransducer.runOut_cons, SequentialTransducer.runOut_nil]
          obtain ⟨qph, qreg, qcnt⟩ := q
          change qph = ParserPhase.inBody at hqph
          subst hqph
          simp [frame_step_end_inBody]
      · obtain ⟨pfx', body, hlen, hreg, hts, hout⟩ := hB
        refine Or.inr (Or.inl ⟨a :: pfx', body, hlen, hreg, ?_, ?_⟩)
        · simp [hts, List.cons_append]
        · have e1 : (frameParser l r taps).runOut q (a :: ts) =
              ((frameParser l r taps).step q a).2 ++
                (frameParser l r taps).runOut ((frameParser l r taps).step q a).1 ts :=
            SequentialTransducer.runOut_cons _ _ _ _
          have e2 : (frameParser l r taps).runOut q (a :: pfx') =
              ((frameParser l r taps).step q a).2 ++
                (frameParser l r taps).runOut ((frameParser l r taps).step q a).1 pfx' :=
            SequentialTransducer.runOut_cons _ _ _ _
          rw [e1, hout, e2, List.append_assoc]
      · obtain ⟨hq'ph, suffix, hts, hlen, hreg, hout⟩ := hC
        rcases step_phase_inBody l r taps q a hq'ph with (rfl | ⟨hqph, b, rfl⟩)
        · have hlen' : suffix.length = l + r := by
            simpa [frame_step_start, freshState, satCount_zero_val] using hlen
          have hreg' : runRegister r taps suffix = 0#r := by
            rw [runRegister_eq_runState_zero]
            simpa [frame_step_start, freshState] using hreg
          have hout' : (frameParser l r taps).runOut
              ((frameParser l r taps).step q FrameToken.start).1 ts =
              suffix.take l := by
            simpa [frame_step_start, freshState, satCount_zero_val] using hout
          have hstate : ((frameParser l r taps).step q FrameToken.start).1 = freshState l r := by
            rw [frame_step_start]
          rw [hstate] at hout'
          refine Or.inr (Or.inl ⟨[], suffix, hlen', hreg', ?_, ?_⟩)
          · rw [hts, List.cons_append]
            simp
          · rw [SequentialTransducer.runOut_cons, frame_step_start]
            simp [hout', SequentialTransducer.runOut_nil]
        · obtain ⟨qph, qreg, qcnt⟩ := q
          have hqph' : qph = ParserPhase.inBody := hqph
          subst hqph'
          simp only [frame_step_bit_inBody] at hlen hreg
          rw [satCount_val] at hlen
          have hmin : min (qcnt.val + 1) (l + r + 1) = qcnt.val + 1 := by omega
          rw [hmin] at hlen
          have hlen' : qcnt.val + (b :: suffix).length = l + r := by
            simp only [List.length_cons]
            omega
          have hreg' : (serialLFSR r taps).runState qreg (b :: suffix) = 0#r := by
            have h1 : (serialLFSR r taps).runState qreg (b :: suffix) =
                (serialLFSR r taps).runState (stepRegister r taps qreg b) suffix := by
              have hc := MealyMachine.runState_cons (serialLFSR r taps) qreg b suffix
              simpa [serial_step_fst] using hc
            rw [h1]
            exact hreg
          have htotal : (FrameToken.bit b :: ts) =
              (b :: suffix).map FrameToken.bit ++ [FrameToken.endTok] := by
            rw [hts]
            simp
          refine Or.inr (Or.inr ⟨rfl, b :: suffix, htotal, hlen', hreg', ?_⟩)
          rw [htotal]
          exact runOut_inBody_bits_end l r taps qreg qcnt (b :: suffix)

/-- A clean encoded body has zero CRC remainder: the register run over
payload plus check bits is the zero register. -/
theorem runRegister_encodedBody_eq_zero (r : ℕ) (taps : BitVec r)
    (bits : List Bool) :
    runRegister r taps (encodedBody r taps bits) = 0#r := by
  have hmain : runRegister r taps (encodedBody r taps bits) =
      (serialLFSR r taps).runState (runRegister r taps bits) (checkBits r taps bits) := by
    unfold encodedBody runRegister
    rw [← MealyMachine.seq_runState_eq _ (bits ++ checkBits r taps bits),
      SequentialTransducer.runState_append]
    simp only [MealyMachine.seq_runState_eq]
  rw [hmain, runState_serial_decomp, checkBits_length]
  have hcheck : (serialLFSR r taps).runState (0#r : BitVec r) (checkBits r taps bits) =
      finalRegister r taps bits := by
    unfold checkBits
    exact runState_zero_toBitsBE r taps (finalRegister r taps bits)
  rw [hcheck, finalRegister_eq_pow, BitVec.xor_self]

/-- **Clean frame round-trip.** A clean encoded payload of declared
length `l` is accepted and returned unchanged. -/
theorem encodedFrame_translates_to_payload (l r : ℕ) (taps : BitVec r)
    (bits : List Bool) (hlen : bits.length = l) :
    (frameParser l r taps).Translates (encodeFrame r taps bits) bits := by
  exact (frame_translates_single l r taps (encodedBody r taps bits) bits).mpr
    ⟨⟨by rw [encodedBody_length, hlen], runRegister_encodedBody_eq_zero r taps bits⟩,
      (encodedBody_take l r taps bits hlen).symm⟩

/-- **Acceptance characterization, restart-aware.** The parser
translates a token list to an output exactly when the token list ends
in one complete frame whose body has length `l + r` and zero CRC
remainder, after an arbitrary prefix. Acceptance and output are
decided separately:
- acceptance depends on the final frame alone: its `start` restarts
  the parser from whatever state the prefix left, so the prefix may
  hold frames that were rejected or cut short;
- the output is everything emitted while reading the prefix, bits of
  such frames included, followed by the first `l` bits of the final
  body.

A single complete frame is the empty-prefix case. The output is the
sequence of payloads when the prefix is a concatenation of clean
frames, as in `twoConsecutiveFrames_translate`. -/
theorem translates_iff_zero_remainder_body (l r : ℕ) (taps : BitVec r)
    (ts : List FrameToken) (out : List Bool) :
    (frameParser l r taps).Translates ts out ↔
      ∃ (pfx : List FrameToken) (body : List Bool),
        body.length = l + r ∧
        runRegister r taps body = 0#r ∧
        ts = pfx ++
          (FrameToken.start :: body.map FrameToken.bit ++ [FrameToken.endTok]) ∧
        out = (frameParser l r taps).runOut (frameParser l r taps).start pfx ++
          body.take l := by
  constructor
  · intro h
    obtain ⟨hacc, hout⟩ := h
    have hphase : ((frameParser l r taps).runState (frameParser l r taps).start ts).phase =
        ParserPhase.done :=
      (frameParser_accept_iff l r taps _).mp hacc
    obtain (hA | hB | hC) :=
      accepted_cases l r taps (frameParser l r taps).start ts hphase
    · obtain ⟨-, hphase2⟩ := hA
      change ParserPhase.awaitingStart = ParserPhase.done at hphase2
      exact ParserPhase.noConfusion hphase2
    · obtain ⟨pfx, body, hlen, hreg, hts, hrun⟩ := hB
      refine ⟨pfx, body, hlen, hreg, hts, ?_⟩
      have hout' : (frameParser l r taps).runOut (frameParser l r taps).start ts = out := by
        simpa only [frameParser_initOut, frameParser_finalOut_apply, List.nil_append,
          List.append_nil] using hout
      rw [hrun] at hout'
      exact hout'.symm
    · obtain ⟨hph, -⟩ := hC
      change ParserPhase.awaitingStart = ParserPhase.inBody at hph
      exact ParserPhase.noConfusion hph
  · intro h
    obtain ⟨pfx, body, hlen, hreg, hts, hout⟩ := h
    rw [hts, hout]
    exact prefix_frame_translates l r taps pfx body hlen hreg

/-- Leading zeros are payload: a payload with a leading zero bit
round-trips at its lengthened declared length. -/
theorem encodedFrame_leading_zero_translates (l r : ℕ) (taps : BitVec r)
    (bits : List Bool) (hlen : bits.length = l) :
    (frameParser (l + 1) r taps).Translates
      (encodeFrame r taps (false :: bits)) (false :: bits) := by
  exact encodedFrame_translates_to_payload (l + 1) r taps (false :: bits) (by simp [hlen])

/-- The empty payload, at declared length `0`, round-trips. -/
theorem encodedFrame_emptyPayload_translates (r : ℕ) (taps : BitVec r) :
    (frameParser 0 r taps).Translates (encodeFrame r taps []) [] := by
  exact encodedFrame_translates_to_payload 0 r taps [] rfl

/-- Two consecutive clean frames are accepted in sequence and return
the two payloads in order; the second `start` restarts the parser. -/
theorem twoConsecutiveFrames_translate (l r : ℕ) (taps : BitVec r)
    (p₁ p₂ : List Bool) (h₁ : p₁.length = l) (h₂ : p₂.length = l) :
    (frameParser l r taps).Translates
      (encodeFrame r taps p₁ ++ encodeFrame r taps p₂) (p₁ ++ p₂) := by
  have haux := two_frame_translates_aux l r taps (encodedBody r taps p₁)
    (encodedBody r taps p₂)
    (by rw [encodedBody_length, h₁]) (runRegister_encodedBody_eq_zero r taps p₁)
    (by rw [encodedBody_length, h₂]) (runRegister_encodedBody_eq_zero r taps p₂)
  rw [encodedBody_take l r taps p₁ h₁, encodedBody_take l r taps p₂ h₂] at haux
  exact haux

/-- A `start` inside a body aborts the partial frame and restarts: a
partial body followed by a clean frame returns the bits already
emitted from the partial body, namely its first `l` bits, followed by
the clean payload. The partial frame is discarded as a frame, but the
bits it emitted before the restart are already in the output and are
not retracted. -/
theorem startInBody_aborts_and_restarts (l r : ℕ) (taps : BitVec r)
    (prefixBits bits : List Bool) (hlen : bits.length = l) :
    (frameParser l r taps).Translates
      (FrameToken.start :: prefixBits.map FrameToken.bit ++
        encodeFrame r taps bits) (prefixBits.take l ++ bits) := by
  exact (translates_iff_zero_remainder_body l r taps _ _).mpr
    ⟨FrameToken.start :: prefixBits.map FrameToken.bit, encodedBody r taps bits,
      by rw [encodedBody_length, hlen], runRegister_encodedBody_eq_zero r taps bits,
      rfl, by rw [start_prefix_runOut, encodedBody_take l r taps bits hlen]⟩

/-- **Wrong length.** After any prefix, a final frame closed by `endTok` whose body does not
have `l + r` bits, fewer or more (past the saturation point of the count included), is
rejected: the token list has no accepted `Translates` result for any output. Rejection happens
only at `endTok`, so `runOut` still contains the bits emitted before validation. -/
theorem wrongLengthBody_rejected (l r : ℕ) (taps : BitVec r) (pfx : List FrameToken)
    (body : List Bool) (hlen : body.length ≠ l + r) (out : List Bool) :
    ¬ (frameParser l r taps).Translates
        (pfx ++ (FrameToken.start :: body.map FrameToken.bit ++ [FrameToken.endTok]))
        out := by
  intro hTrans
  have happ : ((frameParser l r taps).runState (frameParser l r taps).start
      (pfx ++ (FrameToken.start :: body.map FrameToken.bit ++ [FrameToken.endTok]))).phase =
      ParserPhase.done := hTrans.1
  rw [SequentialTransducer.runState_append, List.cons_append, (run_start_cons l r taps _ _).1,
    runState_freshState_frame, ite_eq_right fun h => hlen h.1] at happ
  exact ParserPhase.noConfusion happ

/-- A body with nonzero CRC remainder is rejected, whatever its length:
the frame has no accepted `Translates` result for any output. Rejection
happens only at `endTok`, so `runOut` still contains the first `l` body
bits emitted before validation. -/
theorem nonzeroRemainderBody_rejected (l r : ℕ) (taps : BitVec r)
    (body : List Bool) (hrem : runRegister r taps body ≠ 0#r) (out : List Bool) :
    ¬ (frameParser l r taps).Translates
        (FrameToken.start :: body.map FrameToken.bit ++ [FrameToken.endTok])
        out := by
  intro hTrans
  rw [frame_translates_single] at hTrans
  obtain ⟨⟨_, hReg⟩, _⟩ := hTrans
  exact hrem hReg

end CSLibExt.Coding.FixedLengthCRCFrames
