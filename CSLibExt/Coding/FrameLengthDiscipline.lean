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
`endTok`, this file proves that every malformed frame boundary is rejected:

* a token list without `start`, and, after a prefix that leaves the parser outside a body, a
  nonempty continuation without `start` (`rejects_of_start_not_mem`,
  `rejects_missing_start_after`);
* a final frame closed by `endTok` with fewer than `l + r` body bits
  (`rejects_early_end`) or with more (`rejects_extra_bit`), past the saturation point of the
  length counter included;
* input that ends inside a frame, even after a complete zero-remainder body
  (`rejects_end_of_input_in_frame`).

The reset rule says that `start` moves every state to the fresh candidate state `freshState`
(`step_start`, `run_start_cons`). Consequently a `start` inside an unfinished frame discards
it and opens a new candidate (`translates_restart_iff`): the stream is accepted exactly when
the new candidate is accepted on its own. The parser emits payload bits before it validates a
frame, so the output keeps the bits the unfinished frame emitted before the restart. The
headline `frameParser_length_discipline` bundles the five clauses. CRC-3 instances check
truncated headers, bodies and tails, an extra bit, a missing `endTok`, a resynchronizing
`start` and two consecutive frames.

A misaligned stream whose bits happen to form another valid codeword of the same length is not
detected; that is a limit of any CRC, and no claim is made about it.
-/

@[expose] public section

namespace CSLibExt.Coding.FrameLengthDiscipline

open Cslib.Automata
open CSLibExt.Coding.UnreflectedSerialCRC
open CSLibExt.Coding.FixedLengthCRCFrames

/-- The fresh candidate-frame state entered on every `start`: inside a body, zero
register, zero body bits counted. -/
def freshState (l r : ℕ) : ParserState l r :=
  { phase := ParserPhase.inBody, register := 0#r, count := satCount l r 0 }

/-! ### Reset rule and length counter -/

/-- **Reset rule, one step.** From every state, `start` moves to the fresh candidate state
and emits nothing. -/
theorem step_start (l r : ℕ) (taps : BitVec r) (q : ParserState l r) :
    (frameParser l r taps).step q FrameToken.start = (freshState l r, []) := by
  cases q with
  | mk phase reg count =>
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
  · rw [SequentialTransducer.runState_cons, step_start]
  · simp only [SequentialTransducer.runOut_cons, step_start,
      List.nil_append]

private theorem satCount_step (l r n : ℕ) :
    satCount l r (min n (l + r + 1) + 1) = satCount l r (n + 1) := by
  simp only [satCount, Fin.mk.injEq]
  omega

private theorem satCount_val_lt (l r n : ℕ) :
    (satCount l r n).val < l ↔ n < l := by
  change min n (l + r + 1) < l ↔ n < l
  omega

private theorem step_inBody_bit (l r : ℕ) (taps : BitVec r)
    (reg : BitVec r) (n : ℕ) (b : Bool) :
    (frameParser l r taps).step
        { phase := ParserPhase.inBody, register := reg, count := satCount l r n }
        (FrameToken.bit b) =
      ({ phase := ParserPhase.inBody, register := stepRegister r taps reg b,
         count := satCount l r (n + 1) },
       if n < l then [b] else []) := by
  have hcount : satCount l r ((satCount l r n).val + 1) = satCount l r (n + 1) :=
    satCount_step l r n
  have hcond : (satCount l r n).val < l ↔ n < l := satCount_val_lt l r n
  have h : (frameParser l r taps).step
        { phase := ParserPhase.inBody, register := reg, count := satCount l r n }
        (FrameToken.bit b) =
        ({ phase := ParserPhase.inBody, register := stepRegister r taps reg b,
           count := satCount l r ((satCount l r n).val + 1) },
         if (satCount l r n).val < l then [b] else []) := rfl
  simp only [h, hcount, hcond]

private theorem runState_inBody_bits (l r : ℕ) (taps : BitVec r)
    (reg : BitVec r) (n : ℕ) (body : List Bool) :
    (frameParser l r taps).runState
        { phase := ParserPhase.inBody, register := reg, count := satCount l r n }
        (body.map FrameToken.bit) =
      { phase := ParserPhase.inBody,
        register := (serialLFSR r taps).runState reg body,
        count := satCount l r (n + body.length) } := by
  induction body generalizing reg n with
  | nil => rfl
  | cons b bs ih =>
      simp only [List.map_cons, List.length_cons,
        SequentialTransducer.runState_cons, step_inBody_bit, ih]
      have hmealy : (serialLFSR r taps).runState reg (b :: bs) =
          (serialLFSR r taps).runState (stepRegister r taps reg b) bs := rfl
      have hlen : n + 1 + bs.length = n + (bs.length + 1) := by omega
      rw [hmealy, hlen]

private theorem satCount_val_eq (l r n : ℕ) :
    (satCount l r n).val = l + r ↔ n = l + r := by
  change min n (l + r + 1) = l + r ↔ n = l + r
  constructor <;> intro h <;> omega

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
  induction body generalizing reg n with
  | nil =>
      simp only [List.map_nil, SequentialTransducer.runOut_nil]
      cases h : l - n
      · rfl
      · rfl
  | cons b bs ih =>
      simp only [List.map_cons, SequentialTransducer.runOut_cons,
        step_inBody_bit]
      rw [ih]
      by_cases hn : n < l
      · rw [ite_eq_left hn, List.singleton_append]
        have hln : l - n = (l - (n + 1)) + 1 := by omega
        rw [hln, List.take_succ_cons]
      · rw [ite_eq_right hn, List.nil_append]
        have hz1 : l - (n + 1) = 0 := by omega
        have hz2 : l - n = 0 := by omega
        rw [hz1, hz2, List.take_zero, List.take_zero]

/-- **Length counter.** Reading body bits from the fresh state stays inside the body, with
the serial register of the bits read and the saturating count of how many were read. -/
theorem runState_freshState_bits (l r : ℕ) (taps : BitVec r) (body : List Bool) :
    (frameParser l r taps).runState (freshState l r) (body.map FrameToken.bit) =
      { phase := ParserPhase.inBody, register := runRegister r taps body,
        count := satCount l r body.length } := by
  have h := runState_inBody_bits l r taps (0#r) 0 body
  rw [Nat.zero_add] at h
  exact h

/-- **End-of-frame decision.** A candidate frame closed by `endTok` is accepted exactly when
its body has `l + r` bits and zero CRC register; otherwise the parser fails. -/
theorem runState_freshState_frame_phase (l r : ℕ) (taps : BitVec r) (body : List Bool) :
    ((frameParser l r taps).runState (freshState l r)
        (body.map FrameToken.bit ++ [FrameToken.endTok])).phase =
      if body.length = l + r ∧ runRegister r taps body = 0#r then ParserPhase.done
      else ParserPhase.failed := by
  have hfull : (frameParser l r taps).runState
        { phase := ParserPhase.inBody, register := runRegister r taps body,
          count := satCount l r body.length } [FrameToken.endTok] =
        { phase := (if (satCount l r body.length).val = l + r ∧
            runRegister r taps body = 0#r then ParserPhase.done else ParserPhase.failed),
          register := runRegister r taps body,
          count := satCount l r body.length } := rfl
  rw [SequentialTransducer.runState_append, runState_freshState_bits,
    hfull]
  simp only [satCount_val_eq]

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

/-- **Early `endTok`.** After any prefix, a final frame closed with fewer than `l + r` body
bits is rejected. -/
theorem rejects_early_end (l r : ℕ) (taps : BitVec r) (pfx : List FrameToken)
    (body : List Bool) (hshort : body.length < l + r) (out : List Bool) :
    ¬ (frameParser l r taps).Translates
        (pfx ++ (FrameToken.start :: body.map FrameToken.bit ++ [FrameToken.endTok])) out := by
  intro h
  have happ : ((frameParser l r taps).runState (frameParser l r taps).start
      (pfx ++ (FrameToken.start :: body.map FrameToken.bit ++ [FrameToken.endTok]))).phase =
      ParserPhase.done := h.1
  rw [SequentialTransducer.runState_append, List.cons_append] at happ
  have hreset := (run_start_cons l r taps ((frameParser l r taps).runState
    (frameParser l r taps).start pfx) (body.map FrameToken.bit ++ [FrameToken.endTok])).1
  rw [hreset, runState_freshState_frame_phase] at happ
  have hlen : ¬ (body.length = l + r ∧ runRegister r taps body = 0#r) := by
    rintro ⟨hlen, -⟩
    omega
  rw [ite_eq_right hlen] at happ
  simp at happ

/-- **Extra body bit before `endTok`.** After any prefix, a final frame closed with more
than `l + r` body bits is rejected, beyond the saturation point of the count included. -/
theorem rejects_extra_bit (l r : ℕ) (taps : BitVec r) (pfx : List FrameToken)
    (body : List Bool) (hlong : l + r < body.length) (out : List Bool) :
    ¬ (frameParser l r taps).Translates
        (pfx ++ (FrameToken.start :: body.map FrameToken.bit ++ [FrameToken.endTok])) out := by
  intro h
  have happ : ((frameParser l r taps).runState (frameParser l r taps).start
      (pfx ++ (FrameToken.start :: body.map FrameToken.bit ++ [FrameToken.endTok]))).phase =
      ParserPhase.done := h.1
  rw [SequentialTransducer.runState_append, List.cons_append] at happ
  have hreset := (run_start_cons l r taps ((frameParser l r taps).runState
    (frameParser l r taps).start pfx) (body.map FrameToken.bit ++ [FrameToken.endTok])).1
  rw [hreset, runState_freshState_frame_phase] at happ
  have hlen : ¬ (body.length = l + r ∧ runRegister r taps body = 0#r) := by
    rintro ⟨hlen, -⟩
    omega
  rw [ite_eq_right hlen] at happ
  simp at happ

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

/-- **Frame length discipline (headline).** For the fixed-length token parser: missing
`start`, early `endTok`, an extra body bit before `endTok`, and end of input during a frame
are each rejected after any prefix, and a fresh `start` rejects the unfinished frame and
starts a new candidate. -/
theorem frameParser_length_discipline (l r : ℕ) (taps : BitVec r) :
    (∀ (ts : List FrameToken) (out : List Bool), FrameToken.start ∉ ts →
        ¬ (frameParser l r taps).Translates ts out) ∧
      (∀ (pfx : List FrameToken) (body : List Bool) (out : List Bool), body.length < l + r →
        ¬ (frameParser l r taps).Translates
          (pfx ++ (FrameToken.start :: body.map FrameToken.bit ++ [FrameToken.endTok])) out) ∧
      (∀ (pfx : List FrameToken) (body : List Bool) (out : List Bool), l + r < body.length →
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
    fun pfx body out h => rejects_early_end l r taps pfx body h out,
    fun pfx body out h => rejects_extra_bit l r taps pfx body h out,
    fun pfx body out => rejects_end_of_input_in_frame l r taps pfx body out,
    fun pfx partialBody rest out => translates_restart_iff l r taps pfx partialBody rest out⟩

/-! ### Validation statements (CRC-3, `l = 3`, `r = 3`; the clean body of payload `101`
is `101100`) -/

/-- Truncated header: the empty input and a lone `start` are rejected. -/
theorem crc3_truncated_header_rejected (out : List Bool) :
    ¬ (frameParser 3 3 crc3Taps).Translates [] out ∧
      ¬ (frameParser 3 3 crc3Taps).Translates [FrameToken.start] out := by
  constructor
  · intro h
    have happ : ((frameParser 3 3 crc3Taps).runState (frameParser 3 3 crc3Taps).start
        []).phase = ParserPhase.done := h.1
    exact absurd happ (by decide)
  · intro h
    have happ : ((frameParser 3 3 crc3Taps).runState (frameParser 3 3 crc3Taps).start
        [FrameToken.start]).phase = ParserPhase.done := h.1
    exact absurd happ (by decide)

/-- Truncated body: the payload bits alone, closed by `endTok`, are rejected. -/
theorem crc3_truncated_body_rejected (out : List Bool) :
    ¬ (frameParser 3 3 crc3Taps).Translates
      (FrameToken.start :: [true, false, true].map FrameToken.bit ++ [FrameToken.endTok])
      out := by
  intro h
  have happ : ((frameParser 3 3 crc3Taps).runState (frameParser 3 3 crc3Taps).start
      (FrameToken.start :: [true, false, true].map FrameToken.bit ++
        [FrameToken.endTok])).phase = ParserPhase.done := h.1
  exact absurd happ (by decide)

/-- Truncated tail: the clean frame without its last check bit, closed by `endTok`, and
the clean frame without its `endTok` (missing `endTok`) are both rejected. -/
theorem crc3_truncated_tail_rejected (out : List Bool) :
    ¬ (frameParser 3 3 crc3Taps).Translates
        (FrameToken.start :: [true, false, true, true, false].map FrameToken.bit ++
          [FrameToken.endTok]) out ∧
      ¬ (frameParser 3 3 crc3Taps).Translates
        ((encodeFrame 3 crc3Taps [true, false, true]).dropLast) out := by
  constructor
  · intro h
    have happ : ((frameParser 3 3 crc3Taps).runState (frameParser 3 3 crc3Taps).start
        (FrameToken.start :: [true, false, true, true, false].map FrameToken.bit ++
          [FrameToken.endTok])).phase = ParserPhase.done := h.1
    exact absurd happ (by decide)
  · intro h
    have happ : ((frameParser 3 3 crc3Taps).runState (frameParser 3 3 crc3Taps).start
        ((encodeFrame 3 crc3Taps [true, false, true]).dropLast)).phase =
        ParserPhase.done := h.1
    exact absurd happ (by decide)

/-- One extra bit: the clean body followed by one more bit is rejected, whatever the bit. -/
theorem crc3_one_extra_bit_rejected (b : Bool) (out : List Bool) :
    ¬ (frameParser 3 3 crc3Taps).Translates
      (FrameToken.start ::
        (encodedBody 3 crc3Taps [true, false, true] ++ [b]).map FrameToken.bit ++
          [FrameToken.endTok]) out := by
  cases b
  · intro h
    have happ : ((frameParser 3 3 crc3Taps).runState (frameParser 3 3 crc3Taps).start
        (FrameToken.start ::
          (encodedBody 3 crc3Taps [true, false, true] ++ [false]).map FrameToken.bit ++
            [FrameToken.endTok])).phase = ParserPhase.done := h.1
    exact absurd happ (by decide)
  · intro h
    have happ : ((frameParser 3 3 crc3Taps).runState (frameParser 3 3 crc3Taps).start
        (FrameToken.start ::
          (encodedBody 3 crc3Taps [true, false, true] ++ [true]).map FrameToken.bit ++
            [FrameToken.endTok])).phase = ParserPhase.done := h.1
    exact absurd happ (by decide)

/-- A bit outside any frame: a stray bit after an accepted frame is rejected. -/
theorem crc3_stray_bit_after_frame_rejected (out : List Bool) :
    ¬ (frameParser 3 3 crc3Taps).Translates
      (encodeFrame 3 crc3Taps [true, false, true] ++ [FrameToken.bit true]) out := by
  intro h
  have happ : ((frameParser 3 3 crc3Taps).runState (frameParser 3 3 crc3Taps).start
      (encodeFrame 3 crc3Taps [true, false, true] ++ [FrameToken.bit true])).phase =
      ParserPhase.done := h.1
  exact absurd happ (by decide)

/-- Resynchronizing `start`: a frame cut off after two body bits, followed by the clean
frame of `011`, is accepted; the output is the two emitted bits followed by `011`. -/
theorem crc3_resync_start_accepted :
    (frameParser 3 3 crc3Taps).Translates
      (FrameToken.start :: [true, false].map FrameToken.bit ++
        encodeFrame 3 crc3Taps [false, true, true])
      [true, false, false, true, true] := by
  have hacc : ((frameParser 3 3 crc3Taps).runState (frameParser 3 3 crc3Taps).start
      (FrameToken.start :: [true, false].map FrameToken.bit ++
        encodeFrame 3 crc3Taps [false, true, true])).phase =
      ParserPhase.done := by decide
  have hout : (frameParser 3 3 crc3Taps).runOut (frameParser 3 3 crc3Taps).start
      (FrameToken.start :: [true, false].map FrameToken.bit ++
        encodeFrame 3 crc3Taps [false, true, true]) =
      [true, false, false, true, true] := by decide
  refine ⟨hacc, ?_⟩
  have hinit : (frameParser 3 3 crc3Taps).initOut = [] := rfl
  have hfinal : ∀ q, (frameParser 3 3 crc3Taps).finalOut q = [] := fun q => rfl
  rw [hinit, hfinal, List.nil_append, List.append_nil, hout]

/-- Missing `endTok` followed by a new frame: the complete but unclosed clean body of
`101` is discarded by the next `start`, and the following clean frame of `000` is
accepted. -/
theorem crc3_missing_end_then_frame_accepted :
    (frameParser 3 3 crc3Taps).Translates
      (FrameToken.start :: (encodedBody 3 crc3Taps [true, false, true]).map FrameToken.bit ++
        encodeFrame 3 crc3Taps [false, false, false])
      [true, false, true, false, false, false] := by
  have hacc : ((frameParser 3 3 crc3Taps).runState (frameParser 3 3 crc3Taps).start
      (FrameToken.start ::
        (encodedBody 3 crc3Taps [true, false, true]).map FrameToken.bit ++
        encodeFrame 3 crc3Taps [false, false, false])).phase =
      ParserPhase.done := by decide
  have hout : (frameParser 3 3 crc3Taps).runOut (frameParser 3 3 crc3Taps).start
      (FrameToken.start ::
        (encodedBody 3 crc3Taps [true, false, true]).map FrameToken.bit ++
        encodeFrame 3 crc3Taps [false, false, false]) =
      [true, false, true, false, false, false] := by decide
  refine ⟨hacc, ?_⟩
  have hinit : (frameParser 3 3 crc3Taps).initOut = [] := rfl
  have hfinal : ∀ q, (frameParser 3 3 crc3Taps).finalOut q = [] := fun q => rfl
  rw [hinit, hfinal, List.nil_append, List.append_nil, hout]

/-- Two valid frames, the second with leading zeros, are accepted in order. -/
theorem crc3_two_frames_accepted :
    (frameParser 3 3 crc3Taps).Translates
      (encodeFrame 3 crc3Taps [true, false, true] ++
        encodeFrame 3 crc3Taps [false, false, true])
      [true, false, true, false, false, true] := by
  have hacc : ((frameParser 3 3 crc3Taps).runState (frameParser 3 3 crc3Taps).start
      (encodeFrame 3 crc3Taps [true, false, true] ++
        encodeFrame 3 crc3Taps [false, false, true])).phase =
      ParserPhase.done := by decide
  have hout : (frameParser 3 3 crc3Taps).runOut (frameParser 3 3 crc3Taps).start
      (encodeFrame 3 crc3Taps [true, false, true] ++
        encodeFrame 3 crc3Taps [false, false, true]) =
      [true, false, true, false, false, true] := by decide
  refine ⟨hacc, ?_⟩
  have hinit : (frameParser 3 3 crc3Taps).initOut = [] := rfl
  have hfinal : ∀ q, (frameParser 3 3 crc3Taps).finalOut q = [] := fun q => rfl
  rw [hinit, hfinal, List.nil_append, List.append_nil, hout]

end CSLibExt.Coding.FrameLengthDiscipline
