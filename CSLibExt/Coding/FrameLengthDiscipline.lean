/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Coding.FixedLengthCRCFrames

/-!
# Length and termination discipline of the fixed-length CRC frame parser

For the fixed-length frame parser `frameParser l r taps` over the tokens `start`, `bit b` and
`endTok`, this file proves which ends of a token list are rejected:

* a token list with no `start` at all (`rejects_of_start_not_mem`), and, when a prefix leaves
  the parser outside a body, a nonempty continuation without `start`
  (`rejects_missing_start_after`);
* a final frame closed by `endTok` with fewer or more than `l + r` body bits, past the
  saturation point of the length counter included (`wrongLengthBody_rejected`, in
  `CSLibExt.Coding.FixedLengthCRCFrames`);
* input that ends inside a frame, even after a complete zero-remainder body
  (`rejects_end_of_input_in_frame`).

Each of these is about the end of the stream. A stream is rejected when its last frame is
malformed, while an earlier malformed frame is discarded at the next `start`: it does not make
the stream rejected, and the bits it emitted stay in the accepted output, as
`translates_iff_zero_remainder_body` states.

The reset rule says that `start` moves every state to the fresh candidate state `freshState`
(`frame_step_start`, `run_start_cons`). Consequently a `start` inside an unfinished frame
discards it and opens a new candidate (`translates_restart_iff`): the stream is accepted
exactly when the new candidate is accepted on its own. The parser emits payload bits before it
validates a frame, so the output keeps the bits the unfinished frame emitted before the
restart. The headline `frameParser_length_discipline` bundles four clauses. CRC-3 instances in
the test module `CSLibExtTest.Coding.FrameLengthDiscipline` check truncated headers, bodies and
tails, an extra bit, a missing `endTok`, a resynchronizing `start` and two consecutive
frames.

A misaligned stream whose bits happen to form another valid codeword of the same length is not
detected; that is a limit of any CRC, and no claim is made about it.
-/

@[expose] public section

namespace CSLibExt.Coding.FrameLengthDiscipline

open Cslib.Automata
open CSLibExt.Coding.UnreflectedSerialCRC
open CSLibExt.Coding.FixedLengthCRCFrames

/-! ### Length counter -/

private theorem runState_inBody_bits (l r : ℕ) (taps : BitVec r)
    (reg : BitVec r) (n : ℕ) (body : List Bool) :
    (frameParser l r taps).runState
        { phase := ParserPhase.inBody, register := reg, count := satCount l r n }
        (body.map FrameToken.bit) =
      { phase := ParserPhase.inBody,
        register := (serialLFSR r taps).runState reg body,
        count := satCount l r (n + body.length) } := by
  rw [run_bits_inBody_state, satCount_add]

private theorem step_nostart_failed (l r : ℕ) (taps : BitVec r)
    (q : ParserState l r) (a : FrameToken)
    (hphase : q.phase = ParserPhase.awaitingStart ∨ q.phase = ParserPhase.done ∨
      q.phase = ParserPhase.failed)
    (ha : a ≠ FrameToken.start) :
    ((frameParser l r taps).step q a).1.phase = ParserPhase.failed := by
  cases q with
  | mk phase reg count =>
    cases phase with
    | awaitingStart =>
        cases a with
        | start => exact absurd rfl ha
        | bit b => rfl
        | endTok => rfl
    | inBody => simp at hphase
    | done =>
        cases a with
        | start => exact absurd rfl ha
        | bit b => rfl
        | endTok => rfl
    | failed =>
        cases a with
        | start => exact absurd rfl ha
        | bit b => rfl
        | endTok => rfl

private theorem runState_nostart_mem (l r : ℕ) (taps : BitVec r)
    (q : ParserState l r) (ts : List FrameToken)
    (hphase : q.phase = ParserPhase.awaitingStart ∨ q.phase = ParserPhase.failed)
    (hts : FrameToken.start ∉ ts) :
    ((frameParser l r taps).runState q ts).phase = ParserPhase.awaitingStart ∨
      ((frameParser l r taps).runState q ts).phase = ParserPhase.failed := by
  induction ts generalizing q with
  | nil =>
      simp only [SequentialTransducer.runState_nil]
      exact hphase
  | cons a as ih =>
      simp only [List.mem_cons, not_or] at hts
      obtain ⟨ha', has⟩ := hts
      have ha : a ≠ FrameToken.start := Ne.symm ha'
      rw [SequentialTransducer.runState_cons]
      apply ih
      · have h3 : q.phase = ParserPhase.awaitingStart ∨ q.phase = ParserPhase.done ∨
            q.phase = ParserPhase.failed := by
          rcases hphase with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inr h)
        exact Or.inr (step_nostart_failed l r taps q a h3 ha)
      · exact has

private theorem runOut_inBody_bits (l r : ℕ) (taps : BitVec r)
    (reg : BitVec r) (n : ℕ) (body : List Bool) :
    (frameParser l r taps).runOut
        { phase := ParserPhase.inBody, register := reg, count := satCount l r n }
        (body.map FrameToken.bit) = body.take (l - n) := by
  rw [run_bits_inBody_out, satCount_val]
  congr 1
  omega

/-- **Length counter.** Reading body bits from the fresh state stays inside the body, with
the serial register of the bits read and the saturating count of how many were read. -/
theorem runState_freshState_bits (l r : ℕ) (taps : BitVec r) (body : List Bool) :
    (frameParser l r taps).runState (freshState l r) (body.map FrameToken.bit) =
      { phase := ParserPhase.inBody, register := runRegister r taps body,
        count := satCount l r body.length } := by
  have h := runState_inBody_bits l r taps (0#r) 0 body
  rw [Nat.zero_add] at h
  exact h

/-! ### Rejection clauses -/

/-- **Missing `start`.** A token list with no `start` at all is rejected. -/
theorem rejects_of_start_not_mem (l r : ℕ) (taps : BitVec r) (ts : List FrameToken)
    (hts : FrameToken.start ∉ ts) (out : List Bool) :
    ¬ (frameParser l r taps).Translates ts out := by
  intro h
  have happ : ((frameParser l r taps).runState (frameParser l r taps).start
      ts).phase = ParserPhase.done := h.1
  have hmem := runState_nostart_mem l r taps (frameParser l r taps).start ts
    (Or.inl rfl) hts
  rcases hmem with hmem | hmem <;> rw [hmem] at happ <;> simp at happ

/-- **Missing `start` mid-stream.** When the prefix leaves the parser outside a body (before
any frame, after an accepted frame, or after a failure), a nonempty continuation without a
`start` is rejected: its bits and `endTok`s belong to no frame. -/
theorem rejects_missing_start_after (l r : ℕ) (taps : BitVec r) (pfx ts : List FrameToken)
    (hpfx : ((frameParser l r taps).runState (frameParser l r taps).start pfx).phase ≠
      ParserPhase.inBody)
    (hne : ts ≠ []) (hts : FrameToken.start ∉ ts) (out : List Bool) :
    ¬ (frameParser l r taps).Translates (pfx ++ ts) out := by
  intro h
  have happ : ((frameParser l r taps).runState (frameParser l r taps).start
      (pfx ++ ts)).phase = ParserPhase.done := h.1
  rw [SequentialTransducer.runState_append] at happ
  cases ts with
  | nil => exact absurd rfl hne
  | cons a as =>
      rw [SequentialTransducer.runState_cons] at happ
      simp only [List.mem_cons, not_or] at hts
      obtain ⟨ha', has⟩ := hts
      have ha : a ≠ FrameToken.start := Ne.symm ha'
      revert hpfx
      cases hq : ((frameParser l r taps).runState (frameParser l r taps).start
        pfx).phase with
      | awaitingStart =>
          intro hpfx
          have hstep := step_nostart_failed l r taps _ a (Or.inl hq) ha
          have hmem := runState_nostart_mem l r taps _ as (Or.inr hstep) has
          rcases hmem with hmem | hmem <;> rw [hmem] at happ <;> simp at happ
      | inBody =>
          intro hpfx
          exact hpfx rfl
      | done =>
          intro hpfx
          have hstep := step_nostart_failed l r taps _ a (Or.inr (Or.inl hq)) ha
          have hmem := runState_nostart_mem l r taps _ as (Or.inr hstep) has
          rcases hmem with hmem | hmem <;> rw [hmem] at happ <;> simp at happ
      | failed =>
          intro hpfx
          have hstep := step_nostart_failed l r taps _ a (Or.inr (Or.inr hq)) ha
          have hmem := runState_nostart_mem l r taps _ as (Or.inr hstep) has
          rcases hmem with hmem | hmem <;> rw [hmem] at happ <;> simp at happ

/-- **End of input during a frame.** After any prefix, input that stops after a `start` and
some body bits, with no closing `endTok`, is rejected, even when those bits form a complete
zero-remainder body of length `l + r`. -/
theorem rejects_end_of_input_in_frame (l r : ℕ) (taps : BitVec r) (pfx : List FrameToken)
    (body : List Bool) (out : List Bool) :
    ¬ (frameParser l r taps).Translates
        (pfx ++ (FrameToken.start :: body.map FrameToken.bit)) out := by
  intro h
  have happ : ((frameParser l r taps).runState (frameParser l r taps).start
      (pfx ++ (FrameToken.start :: body.map FrameToken.bit))).phase =
      ParserPhase.done := h.1
  rw [SequentialTransducer.runState_append] at happ
  have hreset := (run_start_cons l r taps ((frameParser l r taps).runState
    (frameParser l r taps).start pfx) (body.map FrameToken.bit)).1
  rw [hreset, runState_freshState_bits] at happ
  simp at happ

/-- **A fresh `start` restarts.** A `start` arriving inside an unfinished frame discards it
and opens a new candidate: the whole stream is accepted exactly when the new candidate
`start :: rest` is accepted on its own, and the output is what was emitted before the
restart (the prefix's output, then the first `l` bits of the unfinished body) followed by
the new candidate's output. -/
theorem translates_restart_iff (l r : ℕ) (taps : BitVec r) (pfx : List FrameToken)
    (partialBody : List Bool) (rest : List FrameToken) (out : List Bool) :
    (frameParser l r taps).Translates
        (pfx ++ (FrameToken.start :: partialBody.map FrameToken.bit) ++
          (FrameToken.start :: rest)) out ↔
      ∃ out' : List Bool, (frameParser l r taps).Translates (FrameToken.start :: rest) out' ∧
        out = (frameParser l r taps).runOut (frameParser l r taps).start pfx ++
          partialBody.take l ++ out' := by
  have hstate : (frameParser l r taps).runState (frameParser l r taps).start
      (pfx ++ (FrameToken.start :: partialBody.map FrameToken.bit) ++
        (FrameToken.start :: rest)) =
      (frameParser l r taps).runState (frameParser l r taps).start
        (FrameToken.start :: rest) := by
    rw [SequentialTransducer.runState_append,
      SequentialTransducer.runState_append]
    have h1 := (run_start_cons l r taps ((frameParser l r taps).runState
      (frameParser l r taps).start pfx) (partialBody.map FrameToken.bit)).1
    rw [h1]
    have h2 := (run_start_cons l r taps ((frameParser l r taps).runState
      (freshState l r) (partialBody.map FrameToken.bit)) rest).1
    rw [h2]
    have h3 := (run_start_cons l r taps (frameParser l r taps).start rest).1
    rw [h3]
  have htake : (frameParser l r taps).runOut (freshState l r)
      (partialBody.map FrameToken.bit) = partialBody.take l := by
    have h0 := runOut_inBody_bits l r taps (0#r) 0 partialBody
    rw [Nat.sub_zero] at h0
    exact h0
  have hout : (frameParser l r taps).runOut (frameParser l r taps).start
      (pfx ++ (FrameToken.start :: partialBody.map FrameToken.bit) ++
        (FrameToken.start :: rest)) =
      (frameParser l r taps).runOut (frameParser l r taps).start pfx ++
        partialBody.take l ++
        (frameParser l r taps).runOut (frameParser l r taps).start
          (FrameToken.start :: rest) := by
    rw [SequentialTransducer.runOut_append,
      SequentialTransducer.runOut_append]
    have h1 := (run_start_cons l r taps ((frameParser l r taps).runState
      (frameParser l r taps).start pfx) (partialBody.map FrameToken.bit)).2
    rw [h1, htake]
    have hs1 := (run_start_cons l r taps ((frameParser l r taps).runState
      (frameParser l r taps).start pfx) (partialBody.map FrameToken.bit)).1
    have hsA : (frameParser l r taps).runState (frameParser l r taps).start
        (pfx ++ (FrameToken.start :: partialBody.map FrameToken.bit)) =
        (frameParser l r taps).runState (freshState l r)
          (partialBody.map FrameToken.bit) := by
      rw [SequentialTransducer.runState_append, hs1]
    rw [hsA]
    have h2 := (run_start_cons l r taps ((frameParser l r taps).runState
      (freshState l r) (partialBody.map FrameToken.bit)) rest).2
    rw [h2]
    have h3 := (run_start_cons l r taps (frameParser l r taps).start rest).2
    rw [h3]
  have hinit : (frameParser l r taps).initOut = [] := rfl
  have hfinal : ∀ q, (frameParser l r taps).finalOut q = [] := fun q => rfl
  constructor
  · intro h
    have hacc := h.1
    have heq := h.2
    rw [hstate, hout, hinit, hfinal, List.nil_append, List.append_nil] at heq
    refine ⟨(frameParser l r taps).runOut (frameParser l r taps).start
      (FrameToken.start :: rest), ⟨?_, ?_⟩, heq.symm⟩
    · rw [hstate] at hacc
      exact hacc
    · rw [hinit, hfinal, List.nil_append, List.append_nil]
  · intro h
    obtain ⟨out', htrans, heq⟩ := h
    have haccB := htrans.1
    have heqB := htrans.2
    rw [hinit, hfinal, List.nil_append, List.append_nil] at heqB
    refine ⟨?_, ?_⟩
    · rw [hstate]
      exact haccB
    · rw [hinit, hfinal, List.nil_append, List.append_nil, hout, heqB]
      exact heq.symm

/-- **Frame length discipline (headline).** For the fixed-length token parser:
- a token list with no `start` at all is rejected;
- after any prefix, a final frame whose body has fewer or more than `l + r` bits is rejected;
- after any prefix, input that ends during a frame is rejected;
- after any prefix, a fresh `start` discards an unfinished frame and opens a new candidate,
  which alone decides acceptance, while the output keeps what was emitted before it.

Every clause is about the end of the stream: an earlier malformed frame is discarded at the
next `start` and does not make the stream rejected. -/
theorem frameParser_length_discipline (l r : ℕ) (taps : BitVec r) :
    (∀ (ts : List FrameToken) (out : List Bool), FrameToken.start ∉ ts →
        ¬ (frameParser l r taps).Translates ts out) ∧
      (∀ (pfx : List FrameToken) (body : List Bool) (out : List Bool), body.length ≠ l + r →
        ¬ (frameParser l r taps).Translates
          (pfx ++ (FrameToken.start :: body.map FrameToken.bit ++ [FrameToken.endTok])) out) ∧
      (∀ (pfx : List FrameToken) (body : List Bool) (out : List Bool),
        ¬ (frameParser l r taps).Translates
          (pfx ++ (FrameToken.start :: body.map FrameToken.bit)) out) ∧
      (∀ (pfx : List FrameToken) (partialBody : List Bool) (rest : List FrameToken)
          (out : List Bool),
        (frameParser l r taps).Translates
            (pfx ++ (FrameToken.start :: partialBody.map FrameToken.bit) ++
              (FrameToken.start :: rest)) out ↔
          ∃ out' : List Bool,
            (frameParser l r taps).Translates (FrameToken.start :: rest) out' ∧
            out = (frameParser l r taps).runOut (frameParser l r taps).start pfx ++
              partialBody.take l ++ out') := by
  exact ⟨fun ts out hts => rejects_of_start_not_mem l r taps ts hts out,
    fun pfx body out h => wrongLengthBody_rejected l r taps pfx body h out,
    fun pfx body out => rejects_end_of_input_in_frame l r taps pfx body out,
    fun pfx partialBody rest out => translates_restart_iff l r taps pfx partialBody rest out⟩

end CSLibExt.Coding.FrameLengthDiscipline
