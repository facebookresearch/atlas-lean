/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Classes
import CSLibExt.Computability.Complexity.CookLevin.Hardness
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.DeriveFintype

/-!
# NEXP is contained in EXPSPACE

A deterministic multi-tape machine explores the computation tree in depth-first order.
It saves one finite record per running step so that it can undo the writes and head movements
before exploring a sibling. If all paths halt or get stuck within time `T`, the simulator visits
at most `2 * (T + 1) + 1` cells per work tape. Applying this bound to nondeterministic
exponential time proves `nexp_subset_expspace`.
-/

namespace MetaMathlibExt.Complexity.KeyTheorems.NEXPSubsetEXPSPACE

open Turing
open Cslib.Complexity.Classes

noncomputable section

variable {k : ℕ} {S : Type} [Fintype S] {w : List Bool}

private abbrev Act (k : ℕ) (S : Type) := Action k Bool S

private instance finiteAction {S : Type} [Finite S] : Finite (Act k S) :=
  Finite.of_injective (fun a : Act k S => (a.inputTape, a.workTapes, a.output, a.state))
    (by rintro ⟨_, _, _, _⟩ ⟨_, _, _, _⟩ h; simpa using h)

private instance actionFintype : Fintype (Act k S) := Fintype.ofFinite _

-- none is the empty output, some true is exactly [true], and some false is any other word.
private def outputClass : List Bool → Option Bool
  | [] => none
  | [true] => some true
  | _ => some false

private def emit (old bit : Option Bool) : Option Bool :=
  match bit with
  | none => old
  | some b => some (old.isNone && b)

private theorem emit_eq (l : List Bool) (b : Option Bool) :
    emit (outputClass l) b = outputClass (l ++ b.toList) := by
  cases b with
  | none => simp [emit]
  | some b =>
    cases l with
    | nil => cases b <;> rfl
    | cons h t => cases h <;> cases t <;> rfl

-- A frame saves the untried siblings and the information needed to undo a step.
private structure Frame (k : ℕ) (S : Type) where
  siblings : Finset (Act k S)
  output : Option Bool
  inputMove : SignType
  work : Fin k → Option Bool × SignType
deriving Fintype

private inductive Control (k : ℕ) (S : Type)
  | start
  | visit (q : Option S) (out : Option Bool) (found : Bool)
  | scan (actions : Finset (Act k S)) (out : Option Bool) (found : Bool)
  | back (found : Bool)
  | pop (found : Bool)
  | restore (f : Frame k S) (found : Bool)
deriving Fintype

-- Besides the simulated tapes, one tape marks the left input boundary. Parallel Boolean
-- history tapes store a frame by marking the tape indexed by that frame.
private abbrev Tape (k : ℕ) (S : Type) := Fin k ⊕ Unit ⊕ Frame k S
private abbrev ntapes (k : ℕ) (S : Type) [Fintype S] := Nat.card (Tape k S)
private def idx := Finite.equivFin (Tape k S)
private abbrev SimCfg (k : ℕ) (S : Type) [Fintype S] (w : List Bool) :=
  Cfg (ntapes k S) Bool (Control k S) w

private def actualMove (sym marker : Option Bool) (d : SignType) : SignType :=
  if sym.isNone && ((marker.isSome && d == .neg) || (marker.isNone && d == .pos)) then 0 else d

private def mark (a : Option (Frame k S)) (f : Frame k S) : Option Bool := by
  classical exact if a = some f then some true else none

private def readFrame (r : Frame k S → Option Bool) : Option (Frame k S) := by
  classical exact if h : ∃ f, r f = some true then some h.choose else none

private theorem read_mark (a : Option (Frame k S)) : readFrame (mark a) = a := by
  classical
  unfold readFrame
  split_ifs with h
  · have := h.choose_spec
    simpa [mark, eq_comm] using this
  · cases a with
    | none => rfl
    | some f => exact (h ⟨f, by simp [mark]⟩).elim

private def tapeFn {α : Type*} (work : Fin k → α) (marker : α) (history : Frame k S → α)
    (i : Fin (ntapes k S)) : α :=
  (idx.symm i).elim work (Sum.elim (fun _ => marker) history)

private abbrev WriteMove := Option (Option Bool) × SignType

private def command (q : Option (Control k S)) (d : SignType := 0)
    (work : Fin k → WriteMove := fun _ => (none, 0))
    (marker : WriteMove := (none, 0))
    (history : Frame k S → WriteMove := fun _ => (none, 0))
    (out : Option Bool := none) : Action (ntapes k S) Bool (Control k S) :=
  ⟨d, tapeFn work marker history, out, q⟩

private def options (M : MultiTapeNTM k Bool S) (q : S) (s : Option Bool)
    (r : Fin k → Option Bool) : Finset (Act k S) := by
  classical exact (Set.toFinite {a | M.Tr q s r a}).toFinset

private def saved (rest : Finset (Act k S)) (out : Option Bool) (d : SignType)
    (r : Fin k → Option Bool) (a : Act k S) : Frame k S :=
  ⟨rest, out, d, fun i => (r i, (a.workTapes i).2)⟩

private def transition (M : MultiTapeNTM k Bool S) (s : Control k S) (input : Option Bool)
    (r : Fin (ntapes k S) → Option Bool) : Action (ntapes k S) Bool (Control k S) := by
  classical
  let work i := r (idx (.inl i))
  let marker := r (idx (.inr (.inl ())))
  let history f := r (idx (.inr (.inr f)))
  exact match s with
  | .start => command (some (.visit (some M.q₀) none false)) (marker := (some (some true), 1))
  | .visit none out b => command (some (.back (b || out == some true)))
  | .visit (some q) out b => command (some (.scan (options M q input work) out b))
  | .scan actions out b =>
    if h : actions.Nonempty then
      let a := h.choose
      let d := actualMove input marker a.inputTape
      let f := saved (actions.erase a) out d work a
      command (some (.visit a.state (emit out a.output) b)) d a.workTapes (none, d)
        (fun j => (some (mark (some f) j), 1))
    else command (some (.back b))
  | .back b => command (some (.pop b)) (history := fun _ => (none, -1))
  | .pop b =>
    match readFrame history with
    | none => command none (out := some b)
    | some f =>
      command (some (.restore f b)) (-f.inputMove) (fun i => (none, -(f.work i).2))
        (none, -f.inputMove) (fun _ => (some none, 0))
  | .restore f b =>
    command (some (.scan f.siblings f.output b)) (work := fun i => (some (f.work i).1, 0))

private def simulator (M : MultiTapeNTM k Bool S) :=
  MultiTapeTM.ofTr .start (transition M)

-- The configuration represented at a node of the search tree.
private def markerTape (z : ℤ) : Option Bool := if z = 0 then some true else none

private def historyTape : List (Frame k S) → Frame k S → ℤ → Option Bool
  | [], _ => fun _ => none
  | f :: fs, j => Function.update (historyTape fs j) fs.length (mark (some f) j)

omit [Fintype S] in
private theorem history_blank (fs : List (Frame k S)) (j : Frame k S) (z : ℤ)
    (h : (fs.length : ℤ) ≤ z) : historyTape fs j z = none := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at h
    simp [historyTape, Function.update_of_ne (show z ≠ (fs.length : ℤ) by omega), ih (by omega)]

private def view (c : Cfg k Bool S w) (fs : List (Frame k S)) (z : ℤ)
    (q : Control k S) : SimCfg k S w :=
  ⟨some q, c.inputPos, tapeFn c.workTapes markerTape (historyTape fs),
    tapeFn c.workTapePos (c.inputPos.val : ℤ) (fun _ => z), []⟩

private abbrev node (c : Cfg k Bool S w) (fs : List (Frame k S)) (q : Control k S) :=
  view c fs fs.length q

private def writeAt (o : Option (Option Bool)) (tape : ℤ → Option Bool) (z : ℤ) :=
  match o with
  | none => tape
  | some bit => Function.update tape z bit

private theorem read_work (c : Cfg k Bool S w) (fs : List (Frame k S)) (z : ℤ)
    (q : Control k S) :
    (view c fs z q).workTapeSymbols =
      tapeFn c.workTapeSymbols (markerTape c.inputPos.val) (fun j => historyTape fs j z) := by
  funext i
  obtain ⟨j, rfl⟩ := idx.surjective i
  rcases j with j | (_ | j) <;> simp [view, Cfg.workTapeSymbols, tapeFn]

private theorem command_eq {c c' : Cfg k Bool S w} {fs fs' : List (Frame k S)} {z z' : ℤ}
    {q q' : Control k S} {d md hd : SignType}
    {work : Fin k → WriteMove} {hist : Frame k S → Option (Option Bool)}
    (hp : moveInputPos c.inputPos d = c'.inputPos)
    (hm : (c.inputPos.val : ℤ) + md.cast = c'.inputPos.val)
    (hh : z + hd.cast = z')
    (ht : ∀ i, writeAt (work i).1 (c.workTapes i) (c.workTapePos i) = c'.workTapes i)
    (hw : ∀ i, c.workTapePos i + (work i).2.cast = c'.workTapePos i)
    (hf : ∀ j, writeAt (hist j) (historyTape fs j) z = historyTape fs' j) :
    (command (some q') d work (none, md) (fun j => (hist j, hd))).apply (view c fs z q) =
      view c' fs' z' q' := by
  refine Cfg.ext ?_ hp ?_ ?_ ?_
  · rfl
  · funext i
    obtain ⟨j, rfl⟩ := idx.surjective i
    rcases j with j | (_ | j)
    · cases h : (work j).1 <;> simpa [Action.apply, command, view, tapeFn, writeAt, h] using ht j
    · simp [Action.apply, command, view, tapeFn]
    · cases h : hist j <;> simpa [Action.apply, command, view, tapeFn, writeAt, h] using hf j
  · funext i
    obtain ⟨j, rfl⟩ := idx.surjective i
    rcases j with j | (_ | j)
    · simpa [Action.apply, command, view, tapeFn] using hw j
    · simpa [Action.apply, command, view, tapeFn] using hm
    · simpa [Action.apply, command, view, tapeFn] using hh
  · rfl

-- The history contains the head movement actually performed, including at either clamped end.
private def delta (c : Cfg k Bool S w) (d : SignType) :=
  actualMove c.inputSymbol (markerTape c.inputPos.val) d

omit [Fintype S] in
private theorem delta_val (c : Cfg k Bool S w) (d : SignType) :
    (c.inputPos.val : ℤ) + (delta c d).cast = (moveInputPos c.inputPos d).val := by
  rw [val_moveInputPos_eq]
  have hb := c.inputPos.isLt
  by_cases hl : c.inputPos.val = 0
  · have hs := inputSymbol_eq_none_of_boundary (cfg := c) (Or.inl hl)
    cases d <;> simp [delta, actualMove, markerTape, hs, hl, SignType.cast] <;> omega
  by_cases hr : c.inputPos.val = w.length + 1
  · have hs := inputSymbol_eq_none_of_boundary (cfg := c) (Or.inr hr)
    have hn : (w.length : ℤ) + 1 ≠ 0 := by omega
    cases d <;> simp [delta, actualMove, markerTape, hs, hr, hn, SignType.cast]
  have hs := inputSymbolInner (cfg := c) (c.inputPos.val - 1) (by omega) (by omega)
  cases d <;> simp [delta, actualMove, hs, SignType.cast] <;> omega

omit [Fintype S] in
private theorem delta_forward (c : Cfg k Bool S w) (d : SignType) :
    moveInputPos c.inputPos (delta c d) = moveInputPos c.inputPos d := by
  have h := delta_val c d
  have hb := (moveInputPos c.inputPos d).isLt
  apply Fin.ext
  have := val_moveInputPos_eq c.inputPos (delta c d)
  omega

omit [Fintype S] in
private theorem delta_back (c : Cfg k Bool S w) (d : SignType) :
    moveInputPos (moveInputPos c.inputPos d) (-(delta c d)) = c.inputPos := by
  have h := delta_val c d
  have hb := c.inputPos.isLt
  apply Fin.ext
  have hm := val_moveInputPos_eq (moveInputPos c.inputPos d) (-(delta c d))
  rw [SignType.coe_neg] at hm
  omega

private theorem step_view (M : MultiTapeNTM k Bool S) (c : Cfg k Bool S w)
    (fs : List (Frame k S)) (z : ℤ) (q : Control k S) :
    (simulator M).step (view c fs z q) = (transition M q c.inputSymbol
      (tapeFn c.workTapeSymbols (markerTape c.inputPos.val)
        (fun j => historyTape fs j z))).apply (view c fs z q) := by
  rw [simulator, Cslib.Turing.MultiTapeTM.step_ofTr]
  simp only [Cslib.Turing.MultiTapeTM.stepWith, read_work]
  rfl

private theorem idle (c : Cfg k Bool S w) (fs : List (Frame k S)) (z : ℤ)
    (q q' : Control k S) :
    (command (some q')).apply (view c fs z q) = view c fs z q' := by
  apply command_eq <;> simp [writeAt]

private theorem step_visit (M : MultiTapeNTM k Bool S) (c : Cfg k Bool S w)
    (fs : List (Frame k S)) (b : Bool) :
    (simulator M).step (node c fs (.visit c.state (outputClass c.output) b)) =
      node c fs (match c.state with
        | none => .back (b || outputClass c.output == some true)
        | some q => .scan (options M q c.inputSymbol c.workTapeSymbols)
            (outputClass c.output) b) := by
  rw [step_view]
  cases h : c.state <;> simp [transition, tapeFn, idle, node]

private theorem step_empty (M : MultiTapeNTM k Bool S) (c : Cfg k Bool S w)
    (fs : List (Frame k S)) (b : Bool) :
    (simulator M).step (node c fs (.scan ∅ (outputClass c.output) b)) = node c fs (.back b) := by
  rw [step_view]
  simp [transition, node, idle]

open scoped Classical in
private def frameAt (c : Cfg k Bool S w) (acts : Finset (Act k S)) (a : Act k S) :=
  saved (acts.erase a) (outputClass c.output) (delta c a.inputTape) c.workTapeSymbols a

private theorem step_push (M : MultiTapeNTM k Bool S) (c : Cfg k Bool S w)
    (fs : List (Frame k S)) (acts : Finset (Act k S)) (h : acts.Nonempty) (b : Bool) :
    let a := h.choose
    (simulator M).step (node c fs (.scan acts (outputClass c.output) b)) =
      node (a.apply c) (frameAt c acts a :: fs)
        (.visit a.state (outputClass (a.apply c).output) b) := by
  dsimp only
  rw [step_view]
  simp only [transition, h, ↓reduceDIte, tapeFn, Equiv.symm_apply_apply, Sum.elim_inl,
    Sum.elim_inr, emit_eq, Action.apply_output]
  apply command_eq
  · exact delta_forward c _
  · exact delta_val c _
  · simp
  · intro i
    cases hwrite : (h.choose.workTapes i).1 <;> simp [writeAt, Action.apply, hwrite]
  · intro i
    rfl
  · intro j
    rfl

private theorem step_back (M : MultiTapeNTM k Bool S) (c : Cfg k Bool S w)
    (fs : List (Frame k S)) (b : Bool) :
    (simulator M).step (node c fs (.back b)) = view c fs (fs.length - 1 : ℤ) (.pop b) := by
  rw [step_view]
  apply command_eq <;> simp [writeAt, sub_eq_add_neg]

private theorem step_pop (M : MultiTapeNTM k Bool S) (c : Cfg k Bool S w)
    (fs : List (Frame k S)) (acts : Finset (Act k S)) (a : Act k S) (b : Bool) :
    let f := frameAt c acts a
    let child := a.apply c
    (simulator M).step (view child (f :: fs) fs.length (.pop b)) =
      node {c with workTapes := child.workTapes} fs (.restore f b) := by
  dsimp only
  rw [step_view]
  have htop (j : Frame k S) : historyTape (frameAt c acts a :: fs) j fs.length =
      mark (some (frameAt c acts a)) j := by simp [historyTape]
  simp only [transition, tapeFn, Equiv.symm_apply_apply, Sum.elim_inr, htop, read_mark]
  apply command_eq
  · exact delta_back c _
  · have hd := delta_val c a.inputTape
    simpa [Action.apply, frameAt, saved, eq_sub_iff_add_eq, ← sub_eq_add_neg] using
      (show ((moveInputPos c.inputPos a.inputTape).val : ℤ) - (delta c a.inputTape).cast =
        c.inputPos.val by omega)
  · simp
  · intro i
    rfl
  · intro i
    simp [Action.apply, frameAt, saved, SignType.coe_neg]
  · intro j
    simp [writeAt, historyTape, Function.update_idem, ← history_blank fs j fs.length le_rfl]

open scoped Classical in
private theorem step_restore (M : MultiTapeNTM k Bool S) (c : Cfg k Bool S w)
    (fs : List (Frame k S)) (acts : Finset (Act k S)) (a : Act k S) (b : Bool) :
    (simulator M).step (node {c with workTapes := (a.apply c).workTapes} fs
      (.restore (frameAt c acts a) b)) =
      node c fs (.scan (acts.erase a) (outputClass c.output) b) := by
  rw [step_view]
  refine command_eq (by simp) (by simp) (by simp) ?_ (by simp) (by simp [writeAt])
  intro i
  cases h : (a.workTapes i).1 <;>
    simp [Action.apply, h, writeAt, frameAt, saved, Cfg.workTapeSymbols]

private def Accepts (M : MultiTapeNTM k Bool S) (c : Cfg k Bool S w) : Prop :=
  ∃ p : M.RunPath w, p.head = c ∧ p.last.Halted ∧ p.last.output = [true]

omit [Fintype S] in
private theorem accepts_halt {M : MultiTapeNTM k Bool S} {c : Cfg k Bool S w}
    (hc : c.Halted) : Accepts M c ↔ c.output = [true] := by
  constructor
  · rintro ⟨p, rfl, _, ho⟩
    rwa [p.last_eq_of_head_halted hc] at ho
  · exact fun h => ⟨.singleton _ c, rfl, hc, h⟩

private theorem accepts_run {M : MultiTapeNTM k Bool S} {c : Cfg k Bool S w} {q : S}
    (hc : c.state = some q) :
    Accepts M c ↔ ∃ a ∈ options M q c.inputSymbol c.workTapeSymbols, Accepts M (a.apply c) := by
  classical
  constructor
  · rintro ⟨p, rfl, hh, ho⟩
    induction p using RelSeries.inductionOn with
    | singleton x => cases hh.symm.trans hc
    | cons p x h _ =>
      simp only [RelSeries.head_cons] at hc ⊢
      change M.Step x p.head at h
      obtain ⟨a, ha, he⟩ := (show ∃ a, M.Tr q _ _ a ∧ p.head = a.apply x by
        simpa [MultiTapeNTM.Step, hc] using h)
      exact ⟨a, by simpa [options] using ha, p, he, by simpa using hh, by simpa using ho⟩
  · rintro ⟨a, ha, p, hp, hh, ho⟩
    have h : M.Step c p.head := by
      simp only [MultiTapeNTM.Step, hc]
      exact ⟨a, by simpa [options] using ha, hp⟩
    exact ⟨p.cons c h, by simp, by simpa using hh, by simpa using ho⟩

open scoped Classical in
private def updated (b : Bool) (P : Prop) : Bool := b || decide P

private theorem out_test (l : List Bool) : (outputClass l == some true) = decide (l = [true]) := by
  cases l with
  | nil => rfl
  | cons h t => cases h <;> cases t <;> simp [outputClass]

private def HeadsInWindow (s : ℕ) (v : SimCfg k S w) := ∀ i, v.workTapePos i ∈ window s

private def ReachesInWindow (M : MultiTapeNTM k Bool S) (s : ℕ) (x y : SimCfg k S w) : Prop :=
  ∃ p : (simulator M).RunPath w, p.head = x ∧ p.last = y ∧ p.InWindow s

private theorem ReachesInWindow.join {M : MultiTapeNTM k Bool S} {s : ℕ} {x y z : SimCfg k S w}
    (h : ReachesInWindow M s x y) (g : ReachesInWindow M s y z) : ReachesInWindow M s x z := by
  obtain ⟨p, hp, hy, hwp⟩ := h
  obtain ⟨q, hq, hz, hwq⟩ := g
  exact ⟨p.smash q (hy.trans hq.symm), by simpa using hp, by simpa using hz, hwp.smash hwq⟩

private theorem single {M : MultiTapeNTM k Bool S} {s : ℕ} {x y : SimCfg k S w}
    (h : (simulator M).step x = y) (hx : HeadsInWindow s x) (hy : HeadsInWindow s y) :
    ReachesInWindow M s x y := by
  let p := RelSeries.singleton ((simulator M).stepRel w) x
  have hs : (simulator M).Step p.last y := MultiTapeTM.step_iff.mpr h
  refine ⟨p.snoc y hs, by simp [p], by simp, fun c hc => ?_⟩
  rcases RelSeries.mem_snoc.mp hc with h | rfl
  · obtain ⟨j, rfl⟩ := h
    exact hx
  · exact hy

private def Bounded (c : Cfg k Bool S w) (h : ℕ) :=
  (∀ i, -(h : ℤ) ≤ c.workTapePos i ∧ c.workTapePos i ≤ h) ∧ c.inputPos.val ≤ h + 1

omit [Fintype S] in
private theorem bounded_step (c : Cfg k Bool S w) (a : Act k S) {h : ℕ}
    (hc : Bounded c h) : Bounded (a.apply c) (h + 1) := by
  refine ⟨fun i => ?_, (val_moveInputPos_le _ _).trans (by have := hc.2; omega)⟩
  have hi := hc.1 i
  have hs := abs_le.mp (workTapePos_apply_le a c i)
  push_cast
  omega

private theorem within_view {c : Cfg k Bool S w} {h T : ℕ} (hc : Bounded c h) (hh : h ≤ T)
    (fs : List (Frame k S)) {z : ℤ} (hz₁ : -(T + 1 : ℤ) ≤ z) (hz₂ : z ≤ T + 1)
    (q : Control k S) : HeadsInWindow (T + 1) (view c fs z q) := by
  intro i
  obtain ⟨j, rfl⟩ := idx.surjective i
  rcases j with j | (_ | j) <;> simp [view, tapeFn, window]
  · have := hc.1 j
    omega
  · have := hc.2
    omega
  · omega

private theorem within_node {c : Cfg k Bool S w} {fs : List (Frame k S)} {T : ℕ}
    (hc : Bounded c fs.length) (hh : fs.length ≤ T) (q : Control k S) :
    HeadsInWindow (T + 1) (node c fs q) := within_view hc hh fs (by omega) (by omega) q

-- Search all the children of a running node. Returning from a child restores its parent's
-- configuration, so every sibling search can reuse the same tape cells.
open scoped Classical in
private theorem scan_tree (M : MultiTapeNTM k Bool S) (c : Cfg k Bool S w)
    (fs : List (Frame k S)) (T : ℕ) (hc : Bounded c fs.length) (ht : fs.length < T)
    (acts : Finset (Act k S))
    (visit : ∀ a ∈ acts, ∀ (f : Frame k S) (b : Bool),
      ReachesInWindow M (T + 1)
        (node (a.apply c) (f :: fs) (.visit a.state (outputClass (a.apply c).output) b))
        (node (a.apply c) (f :: fs) (.back (updated b (Accepts M (a.apply c)))))) (b : Bool) :
    ReachesInWindow M (T + 1) (node c fs (.scan acts (outputClass c.output) b))
      (node c fs (.back (updated b (∃ a ∈ acts, Accepts M (a.apply c))))) := by
  classical
  by_cases h : acts.Nonempty
  · let a := h.choose
    have ha : a ∈ acts := h.choose_spec
    let f := frameAt c acts a
    let child := a.apply c
    let b' := updated b (Accepts M child)
    have hc' : Bounded child (f :: fs).length := bounded_step c a hc
    have ht' : (f :: fs).length ≤ T := ht
    have push := single (step_push M c fs acts h b) (within_node hc ht.le _)
      (within_node hc' ht' _)
    have down := visit a ha f b
    have back : ReachesInWindow M (T + 1) (node child (f :: fs) (.back b'))
        (view child (f :: fs) fs.length (.pop b')) := by
      apply single
      · simpa [child, f] using step_back M child (f :: fs) b'
      · exact within_node hc' ht' _
      · apply within_view hc' ht' _ <;> omega
    have mid : Bounded {c with workTapes := child.workTapes} fs.length := hc
    have pop := single (step_pop M c fs acts a b')
      (within_view hc' ht' _ (by omega) (by omega) _) (within_node mid ht.le _)
    have restore := single (step_restore M c fs acts a b')
      (within_node mid ht.le _) (within_node hc ht.le _)
    have rest := scan_tree M c fs T hc ht (acts.erase a)
      (fun j hj => visit j (Finset.mem_of_mem_erase hj)) b'
    have he : (∃ j ∈ acts, Accepts M (j.apply c)) ↔
        Accepts M child ∨ ∃ j ∈ acts.erase a, Accepts M (j.apply c) := by
      constructor
      · rintro ⟨j, hj, hacc⟩
        by_cases e : j = a
        · subst j; exact Or.inl hacc
        · exact Or.inr ⟨j, Finset.mem_erase.mpr ⟨e, hj⟩, hacc⟩
      · rintro (hacc | ⟨j, hj, hacc⟩)
        · exact ⟨a, ha, hacc⟩
        · exact ⟨j, Finset.mem_of_mem_erase hj, hacc⟩
    have flag : updated b' (∃ j ∈ acts.erase a, Accepts M (j.apply c)) =
        updated b (∃ j ∈ acts, Accepts M (j.apply c)) := by
      rw [propext he]
      by_cases h₁ : Accepts M child <;> simp [b', updated, h₁]
    rw [← flag]
    exact push.join (down.join (back.join (pop.join (restore.join rest))))
  · obtain rfl := Finset.not_nonempty_iff_eq_empty.mp h
    simpa [updated] using single (step_empty M c fs b)
      (within_node hc ht.le _) (within_node hc ht.le _)
termination_by acts.card
decreasing_by exact Finset.card_erase_lt_of_mem ha

-- Induct on the time remaining along the simulated path. At a running configuration the
-- time hypothesis forces this remainder to be positive, even when the node has no children.
private theorem visit_tree (M : MultiTapeNTM k Bool S) {T : ℕ} (ht : M.RunsInTime w T)
    (p : M.ComputationPath w) (fs : List (Frame k S)) (depth : fs.length = p.length)
    (hT : p.length ≤ T) (hc : Bounded p.last fs.length) (b : Bool) :
    ReachesInWindow M (T + 1) (node p.last fs (.visit p.last.state (outputClass p.last.output) b))
      (node p.last fs (.back (updated b (Accepts M p.last)))) := by
  have hw := within_node hc (depth.trans_le hT)
  have step := step_visit M p.last fs b
  cases hq : p.last.state with
  | none =>
    rw [hq] at step
    simpa only [updated, accepts_halt hq, out_test] using single step (hw _) (hw _)
  | some q =>
    rw [hq] at step
    have hlt : p.length < T := by
      by_contra! h
      cases (ht p h).symm.trans hq
    rw [accepts_run hq]
    refine (single step (hw _) (hw _)).join (scan_tree M p.last fs T hc (depth.trans_lt hlt)
      _ ?_ b)
    intro a ha f b'
    have hs : M.Step p.last (a.apply p.last) := by
      simp only [MultiTapeNTM.Step, hq]
      exact ⟨a, by simpa [options] using ha, rfl⟩
    let p' : M.ComputationPath w :=
      ⟨p.toRunPath.snoc _ hs, by simpa using p.head_eq⟩
    have he : p'.last = a.apply p.last := RelSeries.last_snoc _ _ hs
    have hlen : p'.length = p.length + 1 := rfl
    have subtree := visit_tree M ht p' (f :: fs) (by simp [hlen, depth]) (by omega)
      (by rw [he]; exact bounded_step _ _ hc) b'
    simpa only [he, Action.apply_state] using subtree
termination_by T - p.length
decreasing_by simp only [RelSeries.snoc_length]; omega

private theorem step_start (M : MultiTapeNTM k Bool S) (w : List Bool) :
    (simulator M).step ((simulator M).initCfg w) =
      node (M.initCfg w) [] (.visit (some M.q₀) none false) := by
  rw [simulator, Cslib.Turing.MultiTapeTM.step_ofTr]
  change (command (some (.visit (some M.q₀) none false)) (marker := (some (some true), 1))).apply
    (Cfg.init .start w) = _
  refine Cfg.ext rfl (by simp [command, Cfg.init, node, view]) ?_ ?_ rfl
  · funext i
    obtain ⟨j, rfl⟩ := idx.surjective i
    rcases j with j | (_ | j)
    · simp [command, Cfg.init, node, view, tapeFn]
    · funext z
      by_cases hz : z = 0 <;> simp [command, Cfg.init, node, view, tapeFn, hz,
        Function.update, markerTape]
    · simp [command, Cfg.init, node, view, tapeFn, historyTape]
  · funext i
    obtain ⟨j, rfl⟩ := idx.surjective i
    rcases j with j | (_ | j) <;> simp [command, Cfg.init, node, view, tapeFn]

private def finalCfg (M : MultiTapeNTM k Bool S) (w : List Bool) (b : Bool) : SimCfg k S w :=
  {view (M.initCfg w) [] (-1) (.pop b) with state := none, output := [b]}

private theorem step_stop (M : MultiTapeNTM k Bool S) (w : List Bool) (b : Bool) :
    (simulator M).step (view (M.initCfg w) [] (-1) (.pop b)) = finalCfg M w b := by
  rw [step_view]
  have he : readFrame (fun _ : Frame k S => none) = none := by simp [readFrame]
  simp only [transition, tapeFn, Equiv.symm_apply_apply, Sum.elim_inr, historyTape, he]
  refine Cfg.ext rfl (by simp [command, finalCfg]) ?_ ?_ rfl
  · funext i
    obtain ⟨j, rfl⟩ := idx.surjective i
    rcases j with j | (_ | j) <;> simp [command, finalCfg, tapeFn]
  · funext i
    obtain ⟨j, rfl⟩ := idx.surjective i
    rcases j with j | (_ | j) <;> simp [command, finalCfg, tapeFn]

open scoped Classical in
private theorem simulate_input (M : MultiTapeNTM k Bool S) {T : ℕ} (ht : M.RunsInTime w T) :
    ∃ t, (simulator M).ComputesInTimeAndSpace w [decide (Accepts M (M.initCfg w))]
      t (ntapes k S * (2 * (T + 1) + 1)) := by
  let c := M.initCfg w
  let p : M.ComputationPath w := ⟨.singleton _ c, rfl⟩
  have hc : Bounded c 0 := by simp [Bounded, c, Cfg.init]
  have hw := within_node (fs := []) hc (Nat.zero_le T)
  have start := single (step_start M w) (s := T + 1)
    (by intro i; simp [simulator, Cfg.init, mem_window]) (hw _)
  let b := decide (Accepts M c)
  have visit : ReachesInWindow M (T + 1) (node c [] (.visit (some M.q₀) none false))
      (node c [] (.back b)) := by
    have path := visit_tree M ht p [] rfl (Nat.zero_le _) hc false
    change ReachesInWindow M (T + 1) (node c [] (.visit (some M.q₀) none false))
      (node c [] (.back (updated false (Accepts M c)))) at path
    simpa only [updated, Bool.false_or, b] using path
  have hpop : HeadsInWindow (T + 1) (view c [] (-1) (.pop b)) :=
    within_view hc (Nat.zero_le T) _ (by omega) (by omega) _
  have back : ReachesInWindow M (T + 1) (node c [] (.back b)) (view c [] (-1) (.pop b)) := by
    exact single (by simpa using step_back M c [] b) (hw _) hpop
  have stop := single (step_stop M w b) hpop hpop
  obtain ⟨path, hi, hf, hwindow⟩ := start.join (visit.join (back.join stop))
  exact ⟨path.length, MultiTapeTM.computesInTimeAndSpace_iff_exists_runPath.mpr
    ⟨path, hi, hf ▸ rfl, hf ▸ rfl, le_rfl, hwindow.space_le⟩⟩

-- A finite maximum over words of one length supplies the length-indexed time bound in DSPACE.
private theorem simulate (M : MultiTapeNTM k Bool S) {t : ℕ → ℕ} {L : Set (List Bool)}
    (h : NTMDecidesInTime M t L) :
    L ∈ Cslib.Turing.MultiTapeTM.DSPACE (fun n => ntapes k S * (2 * (t n + 1) + 1)) := by
  classical
  choose runtime hr using fun w => simulate_input M (h.1 w)
  let time (n : ℕ) := Finset.univ.sup fun v : Fin n → Bool => runtime (List.ofFn v)
  refine ⟨1, 0, time, ntapes k S, Control k S, inferInstance, simulator M, fun w => ?_⟩
  have he : Accepts M (M.initCfg w) ↔ w ∈ L := by
    rw [h.2 w]
    exact ⟨fun ⟨p, hhead, hh, ho⟩ => ⟨⟨p, hhead⟩, hh, ho⟩,
      fun ⟨p, hh, ho⟩ => ⟨p.toRunPath, p.head_eq, hh, ho⟩⟩
  have hle : runtime w ≤ time w.length := by
    simpa only [List.ofFn_get] using (Finset.le_sup (s := Finset.univ)
      (f := fun v : Fin w.length → Bool => runtime (List.ofFn v)) (Finset.mem_univ w.get))
  obtain ⟨hd, ht, hs⟩ := hr w
  have hout : decide (Accepts M (M.initCfg w)) = MultiTapeTM.indicator L w := by
    rw [propext he]
    by_cases hm : w ∈ L <;> simp [MultiTapeTM.indicator, hm]
  rw [hout] at hd
  exact ⟨hd, ht.mono hle, by simpa using hs⟩

private theorem exponential_bound (p : Polynomial ℕ) :
    ∃ d C : ℕ, ∀ n : ℕ, 2 ^ p.eval n ≤ 2 ^ (n ^ d) + C := by
  obtain ⟨c, e, _, hp⟩ := Cslib.Complexity.CookLevin.Hardness.eval_le_pow p
  refine ⟨(c + 2) * e, 2 ^ p.eval 0 + 2 ^ p.eval 1, fun n => ?_⟩
  by_cases hn : 2 ≤ n
  · have hc : c + 1 ≤ n ^ (c + 1) := (Nat.lt_pow_self hn).le
    have hbase : n + c ≤ n ^ (c + 2) := by
      rw [pow_succ]
      calc
        n + c ≤ (c + 1) * n := by nlinarith
        _ ≤ _ := Nat.mul_le_mul_right _ hc
    have hexp : p.eval n ≤ n ^ ((c + 2) * e) := by
      rw [pow_mul]
      exact (hp n).trans (Nat.pow_le_pow_left hbase _)
    exact (Nat.pow_le_pow_right (by decide) hexp).trans (Nat.le_add_right _ _)
  · have : n = 0 ∨ n = 1 := by omega
    rcases this with rfl | rfl
    · exact (Nat.le_add_right _ _).trans (Nat.le_add_left _ _)
    · exact (Nat.le_add_left _ _).trans (Nat.le_add_left _ _)

/-- **NEXP is contained in EXPSPACE.** Every decision problem in NEXP, the class of
nondeterministic exponential time, also belongs to EXPSPACE, the class of deterministic
exponential space.

Source: S. Arora and B. Barak, Computational
Complexity: A Modern Approach, 2009 (NEXP ⊆ EXPSPACE by exhaustive simulation). -/
public theorem nexp_subset_expspace :
    NEXP ⊆ EXPSPACE := by
  rintro L ⟨p, a, b, k, S, hS, M, hM⟩
  let := Fintype.ofFinite S
  obtain ⟨d, C, hC⟩ := exponential_bound p
  let m := ntapes k S
  refine ⟨d, Cslib.Turing.MultiTapeTM.DSPACE_mono (m * 2 * a)
    (m * (2 * (a * C + b + 1) + 1)) (fun n => ?_) (simulate M hM)⟩
  calc
    m * (2 * (a * 2 ^ p.eval n + b + 1) + 1) ≤
        m * (2 * (a * (2 ^ (n ^ d) + C) + b + 1) + 1) := by gcongr; exact hC n
    _ = _ := by ring

end

end MetaMathlibExt.Complexity.KeyTheorems.NEXPSubsetEXPSPACE
