/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.DensestKSubgraph.Internal.Verifier.Budget
public import CSLibExt.Computability.Complexity.DensestKSubgraph.Internal.Verifier.Finish
public import CSLibExt.Computability.Complexity.DensestKSubgraph.Internal.Verifier.MarkedCursor

/-! # The exact finite verifier and its canonical NP witness -/

@[expose] public section

namespace Cslib.Complexity.DensestKSubgraph.Internal.VerifierMachine

open Turing Function MetaMathlibExt BitstringEncoding TM2Program TM2Embedding
open Cslib.Complexity.DensestKSubgraph.Internal VerifierSpec VerifierBudget
open Cslib.Complexity.PolynomialEncoding Cslib.Complexity.FramedCNF
open Cslib.Complexity.SatVerifier (Sym)
open MetaMathlibExt.ComplexityTheory MetaMathlibExt.Complexity.NPComplete.DensestKSubgraph
open Computability (encodeNat)

/- Disjoint local workspaces, except for explicitly shared ports. -/
inductive K | dec (s : Decode.K) | cur (s : MarkedCursor.K) | row (s : VerifierRow.K)
  | fin (s : VerifierFinish.K)
  deriving DecidableEq

instance : Fintype K where
  elems := Finset.univ.image K.dec ∪ Finset.univ.image K.cur ∪
    Finset.univ.image K.row ∪ Finset.univ.image K.fin
  complete k := by cases k <;> simp

/- Each delegated alphabet is finite. -/
@[reducible] def Γ : K → Type
  | .row k => VerifierRow.Γ k
  | .fin k => VerifierFinish.Γ k
  | _ => Bool

/- The two row-processing stages preserve the mark until the edge has been processed. -/
inductive Lab
  | dec (l : Decode.Lab) | cur (l : MarkedCursor.Lab) | row (l : VerifierRow.Lab)
  | fin (l : VerifierFinish.Lab) | yes | no
  deriving DecidableEq

instance : Fintype Lab where
  elems := {Lab.yes, .no} ∪ Finset.univ.image Lab.dec ∪ Finset.univ.image Lab.cur ∪
    Finset.univ.image Lab.row ∪ Finset.univ.image Lab.fin
  complete l := by cases l <;> simp

/- The three binary headers are kept in the decoder's output slots. -/
abbrev nPort : K := .dec (.n .output)
/- Binary target size. -/
abbrev kPort : K := .dec (.rest (.pair .left))
/- Binary edge threshold. -/
abbrev mPort : K := .dec (.rest (.pair .right))

/- The two already-normalized projected edge streams. -/
abbrev column (b : Bool) : K := .dec (.rest (.items (.output b)))

/- Cursor outputs are the row's two pending endpoint words. -/
def cursorPort : MarkedCursor.K → K
  | .split b .input => column b
  | .split false .left => .row (.word .first)
  | .split true .left => .row (.word .second)
  | s => .cur s

/- The row shares only the normalized vertex bound with the decoder. -/
def rowPort : VerifierRow.K → K
  | .word .bound => nPort
  | s => .row s

/- The final checks read the decoder headers and the row's physical counters. -/
def finishPort : VerifierFinish.K → K
  | .word .n => nPort
  | .word .k => kPort
  | .word .m => mPort
  | .count b => .row (.count b)
  | s => .fin s

/- Initial decoder owns the parser's declared workspace. -/
def decEmb : SEmb (fun _ : Decode.K => Bool) Γ where
  e := K.dec
  inj _ _ h := K.dec.inj h
  ι _ := Equiv.refl _

/- Read the decoded streams and leave the two endpoint words on the row tapes. -/
def curEmb : SEmb (fun _ : MarkedCursor.K => Bool) Γ where
  e := cursorPort
  inj a b h := by
    rcases a with ⟨ra, a⟩ | _ <;> rcases b with ⟨rb, b⟩ | _ <;>
      (try cases ra) <;> (try cases rb) <;> (try cases a) <;> (try cases b) <;> cases h <;> rfl
  ι p := by rcases p with ⟨r, s⟩ | _ <;> (try cases r) <;> (try cases s) <;> exact Equiv.refl _

/- Embedded row processor. -/
def rowEmb : SEmb VerifierRow.Γ Γ where
  e := rowPort
  inj a b h := by
    let inv : K → VerifierRow.K
      | .dec (.n .output) => .word .bound
      | .row r => r
      | _ => .buffer
    have hi (p : VerifierRow.K) : inv (rowPort p) = p := by
      cases p with
      | word w => cases w <;> rfl
      | _ => rfl
    exact (hi a).symm.trans ((congrArg inv h).trans (hi b))
  ι p := by cases p with | word p => cases p <;> exact Equiv.refl _ | _ => exact Equiv.refl _

/- Embedded threshold checker. -/
def finEmb : SEmb VerifierFinish.Γ Γ where
  e := finishPort
  inj a b h := by
    let inv : K → VerifierFinish.K
      | .dec (.n .output) => .word .n
      | .dec (.rest (.pair .left)) => .word .k
      | .dec (.rest (.pair .right)) => .word .m
      | .row (.count b) => .count b
      | .fin r => r
      | _ => .word .n
    have hi (p : VerifierFinish.K) : inv (finishPort p) = p := by
      cases p with
      | word w => cases w <;> rfl
      | _ => rfl
    exact (hi a).symm.trans ((congrArg inv h).trans (hi b))
  ι p := by cases p with | word p => cases p <;> exact Equiv.refl _ | _ => exact Equiv.refl _

/- Decode failure rejects; success starts the marked scan. -/
def decLabel : Decode.Lab → Lab
  | .good => .cur .next
  | .bad => .no
  | l => .dec l

/- Read a row, finish when both streams have ended, or reject a length mismatch. -/
def curLabel : MarkedCursor.Lab → Lab
  | .item b => .row (.cmp .first b (.copy .a))
  | .finish => .fin (.test .bound (.copy .a))
  | .bad => .no
  | l => .cur l

/- Repeat on success; otherwise the graph is malformed. -/
def rowLabel : VerifierRow.Lab → Lab
  | .done => .cur .next
  | .bad => .no
  | l => .row l

/- The threshold checker determines the final verdict. -/
def finLabel : VerifierFinish.Lab → Lab
  | .yes => .yes
  | .no => .no
  | l => .fin l

/- The verifier is a fixed finite TM2 program, not an abstract cost annotation. -/
def prog : Lab → TM2.Stmt Γ Lab Bool
  | .dec l => mapS decEmb decLabel (Decode.prog l)
  | .cur l => mapS curEmb curLabel (MarkedCursor.prog l)
  | .row l => mapS rowEmb rowLabel (VerifierRow.prog l)
  | .fin l => mapS finEmb finLabel (VerifierFinish.prog l)
  | .yes | .no => .halt

private theorem dec_ok : Embeds decEmb decLabel Decode.prog prog := by
  intro l; cases l <;> first | exact Or.inl rfl | exact Or.inr rfl

private theorem cur_ok : Embeds curEmb curLabel MarkedCursor.prog prog := by
  intro l; cases l <;> first | exact Or.inl rfl | exact Or.inr rfl

private theorem row_ok : Embeds rowEmb rowLabel VerifierRow.prog prog := by
  intro l; cases l <;> first | exact Or.inl rfl | exact Or.inr rfl

private theorem fin_ok : Embeds finEmb finLabel VerifierFinish.prog prog := by
  intro l; cases l <;> exact Or.inl rfl

/- Tape agreement between iterations; unused parser scratch need not be inspected. -/
structure Ready (n k m : ℕ) (seen : Seen) (es : List (ℕ × ℕ)) (w u v : List Bool)
    (S : (s : K) → List (Γ s)) : Prop where
  cursor : Agree curEmb (MarkedCursor.st (bitEncode (es.map Prod.fst))
    (bitEncode (es.map Prod.snd)) u v w) S
  row : Agree rowEmb (VerifierRow.stk (VerifierRow.snap n u v seen)) S
  finish : Agree finEmb (VerifierFinish.st n k m seen.selected seen.vertices.length) S

private theorem cur_ne_fin (j : MarkedCursor.K) (q : VerifierFinish.K) :
    curEmb.e j ≠ finEmb.e q := by
  rcases j with ⟨b, j⟩ | _ <;> (try cases b) <;> (try cases j) <;>
    cases q with
    | word w => cases w <;> simp [curEmb, finEmb, cursorPort, finishPort]
    | _ => simp [curEmb, finEmb, cursorPort, finishPort]

private theorem after_cursor {n k m : ℕ} {seen : Seen} {es es' : List (ℕ × ℕ)}
    {w w' u v : List Bool} {S T : (j : K) → List (Γ j)}
    (h : Ready n k m seen es w [] [] S) (hf : Frame curEmb S T)
    (hc : Agree curEmb (MarkedCursor.st (bitEncode (es'.map Prod.fst))
      (bitEncode (es'.map Prod.snd)) u v w') T) : Ready n k m seen es' w' u v T := by
  refine ⟨hc, ?_, fun q => (hf _ (fun j => cur_ne_fin j q)).trans (h.finish q)⟩
  intro q
  cases q with
  | word t =>
    cases t with
    | first => exact hc (.split false .left)
    | second => exact hc (.split true .left)
    | bound =>
      refine (hf nPort ?_).trans (h.row (.word .bound))
      intro j
      rcases j with ⟨b, j⟩ | _ <;> (try cases b) <;> (try cases j) <;> decide
  | dict b i =>
    refine (hf _ ?_).trans (h.row (.dict b i))
    intro j
    rcases j with ⟨r, j⟩ | _ <;> (try cases r) <;> (try cases j) <;>
      simp [rowEmb, rowPort, curEmb, cursorPort]
  | compare i =>
    refine (hf _ ?_).trans (h.row (.compare i))
    intro j
    rcases j with ⟨r, j⟩ | _ <;> (try cases r) <;> (try cases j) <;>
      simp [rowEmb, rowPort, curEmb, cursorPort]
  | count b =>
    refine (hf _ ?_).trans (h.row (.count b))
    intro j
    rcases j with ⟨r, j⟩ | _ <;> (try cases r) <;> (try cases j) <;>
      simp [rowEmb, rowPort, curEmb, cursorPort]
  | buffer =>
    refine (hf _ ?_).trans (h.row .buffer)
    intro j
    rcases j with ⟨r, j⟩ | _ <;> (try cases r) <;> (try cases j) <;> decide

private theorem after_row {n k m : ℕ} {seen seen' : Seen} {es : List (ℕ × ℕ)}
    {w u v : List Bool} {S T : (j : K) → List (Γ j)}
    (h : Ready n k m seen es w u v S) (hf : Frame rowEmb S T)
    (hr : Agree rowEmb (VerifierRow.stk (VerifierRow.snap n [] [] seen')) T) :
    Ready n k m seen' es w [] [] T := by
  refine ⟨?_, hr, ?_⟩
  · intro j
    rcases j with ⟨b, s⟩ | _
    · cases b <;> cases s
      case false.left => exact hr (.word .first)
      case true.left => exact hr (.word .second)
      all_goals
        refine (hf _ ?_).trans (h.cursor _)
        intro q
        cases q with
        | word q => cases q <;> decide
        | dict b s => simp [rowEmb, rowPort, curEmb, cursorPort]
        | compare s => simp [rowEmb, rowPort, curEmb, cursorPort]
        | count b => simp [rowEmb, rowPort, curEmb, cursorPort]
        | buffer => decide
    · refine (hf _ ?_).trans (h.cursor .mask)
      intro q
      cases q with
      | word q => cases q <;> decide
      | _ => simp [rowEmb, rowPort, curEmb, cursorPort]
  · intro q
    cases q with
    | count b => cases b <;> exact hr (.count _)
    | word t =>
      cases t with
      | n => exact hr (.word .bound)
      | k | m | binaryCount =>
        refine (hf _ ?_).trans (h.finish (.word _))
        intro p
        cases p with
        | word p => cases p <;> simp [rowEmb, rowPort, finEmb, finishPort]
        | _ => simp [rowEmb, rowPort, finEmb, finishPort]
    | code s =>
      refine (hf _ ?_).trans (h.finish (.code s))
      intro p
      cases p with
      | word p => cases p <;> simp [rowEmb, rowPort, finEmb, finishPort]
      | _ => simp [rowEmb, rowPort, finEmb, finishPort]
    | cmp s =>
      refine (hf _ ?_).trans (h.finish (.cmp s))
      intro p
      cases p with
      | word p => cases p <;> simp [rowEmb, rowPort, finEmb, finishPort]
      | _ => simp [rowEmb, rowPort, finEmb, finishPort]

open Classical in
/- The composed scan has a polynomial total run, including both malformed mask paths. -/
theorem loop_run (B n k m : ℕ) (es : List (ℕ × ℕ)) (w : List Bool) (seen : Seen)
    (v : Bool) (S : (j : K) → List (Γ j)) (h : Ready n k m seen es w [] [] S)
    (hz : Fits B n k m es) (hb : History B seen es) :
    ∃ z T, RunLe prog (es.length * VerifierBudget.row B + VerifierBudget.finish B)
      ⟨some (.cur .next), v, S⟩
      ⟨some (if Accept n k m seen es w then .yes else .no), z, T⟩ := by
  induction es generalizing w seen v S with
  | nil =>
    cases w with
    | nil =>
      have r₁ := MarkedCursor.run_empty v
      obtain ⟨T, hr₁, _, f₁⟩ := runLe_embed curLabel cur_ok (r₁.le le_rfl) h.cursor
      have hfin : Agree finEmb (VerifierFinish.st n k m seen.selected seen.vertices.length) T :=
        fun q => (f₁ _ (fun j => cur_ne_fin j q)).trans (h.finish q)
      obtain ⟨z, U, rr⟩ := VerifierFinish.run n k m seen.selected seen.vertices.length false
      obtain ⟨V, hr₂, _, _⟩ := runLe_embed finLabel fin_ok rr hfin
      have hl : finLabel (if k ≤ n ∧ m ≤ seen.selected ∧ seen.vertices.length ≤ k
          then .yes else .no) = (if Accept n k m seen [] [] then .yes else .no) := by
        simp only [accept_nil n k m seen [] hb.nodup, true_and]
        split <;> rfl
      rw [hl] at hr₂
      refine ⟨z, V, (hr₁.trans hr₂).mono ?_⟩
      simp only [List.length_nil, Nat.zero_mul, Nat.zero_add]
      exact finish_le hb hz.1 hz.2.1 hz.2.2.1
    | cons b w =>
      have r₁ := MarkedCursor.run_extra b w v
      obtain ⟨T, hr₁, _, _⟩ := runLe_embed curLabel cur_ok (r₁.le le_rfl) h.cursor
      have hno : ¬ Accept n k m seen [] (b :: w) := by
        simp [accept_nil n k m seen (b :: w) hb.nodup]
      refine ⟨true, T, ?_⟩
      simpa only [hno, ite_false, List.length_nil, Nat.zero_mul, Nat.zero_add, curLabel] using
        hr₁.mono (one_le B)
  | cons e es ih =>
    cases w with
    | nil =>
      have rn : ∃ b u, bitEncode ((e :: es).map Prod.fst) = b :: u := by
        change ∃ b u, delimit (bitEncode e.1) ++ bitEncode (es.map Prod.fst) = b :: u
        cases bitEncode e.1 <;> exact ⟨_, _, rfl⟩
      obtain ⟨b, u, hu⟩ := rn
      have r₁ := MarkedCursor.run_missing b u (bitEncode ((e :: es).map Prod.snd)) v
      obtain ⟨T, hr₁, _, _⟩ := runLe_embed curLabel cur_ok (r₁.le le_rfl)
        (by rw [← hu]; exact h.cursor)
      refine ⟨false, T, ?_⟩
      simp only [reject_missing n k m seen e es, ite_false]
      exact hr₁.mono ((one_le B).trans (Nat.le_add_left _ _))
    | cons b w =>
      obtain ⟨z₁, rr₁⟩ := MarkedCursor.run_cons e es b w v
      obtain ⟨S₁, hr₁, a₁, f₁⟩ := runLe_embed curLabel cur_ok (rr₁.le le_rfl) h.cursor
      have hnew := after_cursor h f₁ a₁
      obtain ⟨z₂, R, rr₂, a₂⟩ := VerifierRow.run n e seen b z₁
      obtain ⟨S₂, hr₂, a₂', f₂⟩ := runLe_embed rowLabel row_ok rr₂ hnew.row
      have he := hz.2.2.2 e (by simp)
      have hcost := row_le hb hz.1 he
      by_cases hok : Valid n e ∧ GraphKeys.key e ∉ seen.edges
      · have hn : Ready n k m (advance seen e b) es w [] [] S₂ := by
          rw [a₂ hok] at a₂'
          exact after_row hnew f₂ a₂'
        have hfits : Fits B n k m es := ⟨hz.1, hz.2.1, hz.2.2.1,
          fun a ha => hz.2.2.2 a (List.mem_cons_of_mem _ ha)⟩
        obtain ⟨z, T, hr₃⟩ := ih w (advance seen e b) z₂ S₂ hn hfits (history_next hb he hok.2 b)
        simp only [hok, rowLabel] at hr₂
        have ha : Accept n k m seen (e :: es) (b :: w) ↔
            Accept n k m (advance seen e b) es w := by
          constructor
          · intro hp
            exact ((accept_cons n k m seen e es b w).mp hp).2.2
          · intro hp
            exact (accept_cons n k m seen e es b w).mpr ⟨hok.1, hok.2, hp⟩
        refine ⟨z, T, ?_⟩
        simp only [ha]
        apply (((hr₁.trans hr₂).mono hcost).trans hr₃).mono
        rw [List.length_cons, Nat.succ_mul]
        omega
      · have ha : ¬ Accept n k m seen (e :: es) (b :: w) := by
          intro hp
          have hc := (accept_cons n k m seen e es b w).mp hp
          exact hok ⟨hc.1, hc.2.1⟩
        simp only [hok, ite_false, rowLabel] at hr₂
        refine ⟨z₂, S₂, ?_⟩
        simp only [ha, ite_false]
        apply ((hr₁.trans hr₂).mono hcost).mono
        rw [List.length_cons, Nat.succ_mul]
        omega

end Cslib.Complexity.DensestKSubgraph.Internal.VerifierMachine
