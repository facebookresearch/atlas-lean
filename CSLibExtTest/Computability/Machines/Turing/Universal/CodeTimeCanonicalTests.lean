/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Machines.Turing.Universal.CodeTimeCanonical

/-!
# Canonical CodeTime clients and boundary probes

The unchanged `constFalse` code is the dirty-left regression: its old step-for-step machine
fails `Outputs` on `[true]`, but the canonical machine succeeds. The second code moves left of
its input, writes a dirty work symbol there, returns, and traverses its real binary input.
Cleanup is also tested with marked blanks between dirty cells on *both* sides of the answer.
All executable equality probes are kernel-reduced, not `native_decide`.
-/

@[expose] public section

set_option autoImplicit false

namespace CSLibExtTest.Computability.Machines.Turing.Universal.CodeTimeCanonical

open Relation Cslib.Turing Cslib.Turing.Universal
open Cslib.Turing.SingleTapeTM
open _root_.Turing

/-- Iterate the actual canonical step function, with no hold-on-halt convention. -/
def runCode (c : Code) (x : List Bool) (n : ℕ) : Option c.canonicalSingleTapeTM.Cfg :=
  (flip bind c.canonicalSingleTapeTM.step)^[n]
    (some (c.canonicalSingleTapeTM.initCfg (x.map c.canonicalInputSym)))

/-- The old negative case is retained: source halting alone does not mean canonical output. -/
example : ¬Code.constFalse.singleTapeTM.Outputs ([true].map Code.constFalse.inputSym)
    [Code.constFalse.inputSym false] := fun h ↦
  absurd ((Code.constFalse_decidesWithin.outputs_singleTapeTM_iff [true]).1 h 2 (by decide))
    (by decide)

/-- The same unmodified dirty-left code now has canonical outputs on *every* word. -/
example (x : List Bool) :
    Code.constFalse.canonicalSingleTapeTM.OutputsWithinTime (x.map Code.constFalse.canonicalInputSym)
      [Code.constFalse.canonicalInputSym false] (6 * x.length + 14) := by
  convert Code.constFalse_decidesWithin.outputsWithinTime_canonicalSingleTapeTM x using 1
  simp only [canonicalTime]
  omega

/-- Empty input really writes an answer and leaves both half-tapes blank. -/
example : runCode Code.constFalse [] 10 =
    some (Code.constFalse.canonicalSingleTapeTM.haltCfg
      [Code.constFalse.canonicalInputSym false]) :=
  rfl

/-- Dirty-left `[true]` has the canonical tape after exactly fourteen primitive transitions. -/
example : runCode Code.constFalse [true] 14 =
    some (Code.constFalse.canonicalSingleTapeTM.haltCfg
      [Code.constFalse.canonicalInputSym false]) :=
  rfl

/-- One transition earlier it is still running; the probe exercises the final anchor restoration. -/
example : ((runCode Code.constFalse [true] 13).map fun d ↦ d.state.isNone) = some false := rfl

/-- A mixed, genuinely traversed input also ends with the canonical answer and empty halves. -/
example : runCode Code.constFalse [true, false, true] 22 =
    some (Code.constFalse.canonicalSingleTapeTM.haltCfg
      [Code.constFalse.canonicalInputSym false]) :=
  rfl

/-- After the actual halting transition, the next step has no successor. -/
example : runCode Code.constFalse [true] 15 = none := rfl

/-- Zero time cannot produce a canonical answer, even on empty input. -/
example (c : Code) (x : List Bool) (b : Bool) :
    ¬c.canonicalSingleTapeTM.OutputsWithinTime (x.map c.canonicalInputSym)
      [c.canonicalInputSym b] 0 := by
  intro h
  have hs := congrArg (fun d : c.canonicalSingleTapeTM.Cfg ↦ d.state) h.zero
  cases hs

/-- An immediate source halt still goes through marked simulation and canonical cleanup. -/
example : (⟨[]⟩ : Code).canonicalSingleTapeTM.OutputsWithinTime
    ([true].map (⟨[]⟩ : Code).canonicalInputSym) [(⟨[]⟩ : Code).canonicalInputSym true] 12 := by
  have hr : RelatesWithinSteps (⟨[]⟩ : Code).singleTapeTM.TransitionRelation
      ((⟨[]⟩ : Code).singleTapeTM.initCfg [(⟨[]⟩ : Code).inputSym true])
      ((⟨[]⟩ : Code).singleTapeTM.haltCfg [(⟨[]⟩ : Code).inputSym true]) 1 := .single rfl
  simpa [Code.canonicalInputSym, List.map_map, Function.comp_def] using
    canonicalComputer_outputsHeadWithinTime (⟨[]⟩ : Code).singleTapeTM hr rfl rfl

/-- An immediately halting source with a blank head does not manufacture a binary answer. -/
example : runCode (⟨[]⟩ : Code) [] 8 =
    some ((⟨[]⟩ : Code).canonicalSingleTapeTM.haltCfg [Canonical.Symbol.cell none]) := rfl

/-- Explicit two-sided work, with source blanks between dirty cells. Both sweeps must cross them. -/
example : RelatesInSteps (idComputer (Symbol := Bool)).canonicalComputer.TransitionRelation
    ⟨some .cleanup, Canonical.markedTape (some false)
      [some true, none, some false, none] [none, some true, none, some false]⟩
    ((idComputer (Symbol := Bool)).canonicalComputer.haltCfg [Canonical.embed false]) 21 :=
  Canonical.cleanup_relatesInSteps _ _ _ _

/-- The exact four-pass cleanup on that tape is kernel-reduced independently of its run theorem. -/
example : (flip bind (idComputer (Symbol := Bool)).canonicalComputer.step)^[21]
    (some ⟨some .cleanup, Canonical.markedTape (some false)
      [some true, none, some false, none] [none, some true, none, some false]⟩) =
    some ((idComputer (Symbol := Bool)).canonicalComputer.haltCfg [Canonical.embed false]) := rfl

/-- Move left of the input, write work symbol `7`, return, then scan right and answer false. -/
def leftThenFalse : Code :=
  ⟨[[some (2, 0), some (2, 0), some (2, 0)], [], [some (3, 9)],
    List.replicate 7 none ++ [some (4, 1)],
    [some (1, 3), some (4, 1), some (4, 1)]]⟩

private theorem leftThenFalse_prefix (x : List Bool) :
    leftThenFalse.stepOrStay^[3] (Code.init x) =
      ⟨4, [7], (input x).headI, (input x).tail⟩ := by
  cases x with
  | nil => rfl
  | cons b x => cases b <;> rfl

private theorem leftThenFalse_scan (v : List Bool) (L : List ℕ) :
    leftThenFalse.stepOrStay^[v.length + 1] ⟨4, L, (input v).headI, (input v).tail⟩ =
      ⟨1, (input v).reverse ++ L, 1, []⟩ := by
  induction v generalizing L with
  | nil => rfl
  | cons b v ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have hs : leftThenFalse.stepOrStay
        ⟨4, L, (input (b :: v)).headI, (input (b :: v)).tail⟩ =
        ⟨4, bitSym b :: L, (input v).headI, (input v).tail⟩ := by
      cases b <;> cases v <;> rfl
    rw [hs, ih]
    simp [input]

/-- The traversing source decider has a dirty left tape, on empty as well as nonempty inputs. -/
theorem leftThenFalse_decidesWithin :
    leftThenFalse.DecidesWithin (fun _ ↦ false) (fun n ↦ n + 4) := by
  intro x
  rw [Code.evalSteps_eq_some_iff_output, Code.cfgAfter]
  dsimp only
  rw [show x.length + 4 = (x.length + 1) + 3 by omega, Function.iterate_add_apply,
    leftThenFalse_prefix, leftThenFalse_scan]
  exact ⟨rfl, rfl⟩

/-- Its actual source output is correct, but its visited left cells are not blank. -/
example : leftThenFalse.cfgAfter [true, false] 6 = ⟨1, [1, 2, 7], 1, []⟩ := rfl

/-- Canonical class construction applies without a clean-left assumption to this traversing code. -/
example (x : List Bool) :
    leftThenFalse.canonicalSingleTapeTM.OutputsWithinTime (x.map leftThenFalse.canonicalInputSym)
      [leftThenFalse.canonicalInputSym false] (6 * x.length + 26) := by
  convert leftThenFalse_decidesWithin.outputsWithinTime_canonicalSingleTapeTM x using 1
  simp only [canonicalTime]
  omega

/-- The empty traversing source still visits and erases its left work cell. -/
example : runCode leftThenFalse [] 18 =
    some (leftThenFalse.canonicalSingleTapeTM.haltCfg [leftThenFalse.canonicalInputSym false]) := rfl

/-- Left boundary, dirty work symbol, return and real right traversal are all exercised. -/
example : runCode leftThenFalse [true, false] 26 =
    some (leftThenFalse.canonicalSingleTapeTM.haltCfg [leftThenFalse.canonicalInputSym false]) := rfl

/-- Visit the left work cell, then erase each input symbol before moving right. The final dirty
work symbol is separated from the answer by source blanks, so an unmarked cleanup would stop early. -/
def leftEraseFalse : Code :=
  ⟨[[some (2, 0), some (2, 0), some (2, 0)], [], [some (3, 9)],
    List.replicate 7 none ++ [some (4, 1)],
    [some (1, 3), some (5, 2), some (5, 2)], [some (4, 1)]]⟩

private theorem leftEraseFalse_prefix (x : List Bool) :
    leftEraseFalse.stepOrStay^[3] (Code.init x) =
      ⟨4, [7], (input x).headI, (input x).tail⟩ := by
  cases x with
  | nil => rfl
  | cons b x => cases b <;> rfl

private theorem leftEraseFalse_scan (v : List Bool) (L : List ℕ) :
    leftEraseFalse.stepOrStay^[2 * v.length + 1] ⟨4, L, (input v).headI, (input v).tail⟩ =
      ⟨1, List.replicate v.length 0 ++ L, 1, []⟩ := by
  induction v generalizing L with
  | nil => rfl
  | cons b v ih =>
    rw [List.length_cons, show 2 * (v.length + 1) + 1 = (2 * v.length + 1) + 2 by omega,
      Function.iterate_add_apply]
    have hs : leftEraseFalse.stepOrStay^[2]
        ⟨4, L, (input (b :: v)).headI, (input (b :: v)).tail⟩ =
        ⟨4, 0 :: L, (input v).headI, (input v).tail⟩ := by
      cases b <;> rfl
    rw [hs, ih]
    simp [List.replicate_succ']

/-- Erasing the real input still decides false, but does not make the dirty work cell disappear. -/
theorem leftEraseFalse_decidesWithin :
    leftEraseFalse.DecidesWithin (fun _ ↦ false) (fun n ↦ 2 * n + 4) := by
  intro x
  rw [Code.evalSteps_eq_some_iff_output, Code.cfgAfter]
  dsimp only
  rw [show 2 * x.length + 4 = (2 * x.length + 1) + 3 by omega,
    Function.iterate_add_apply, leftEraseFalse_prefix, leftEraseFalse_scan]
  exact ⟨rfl, rfl⟩

/-- A real run produces the source blank gap, rather than merely starting cleanup on a fixture. -/
example : leftEraseFalse.cfgAfter [true, false] 8 = ⟨1, [0, 0, 7], 1, []⟩ := rfl

/-- The old output convention bridge rejects this dirty-left run despite the leading blank. -/
example : ¬leftEraseFalse.singleTapeTM.Outputs ([true].map leftEraseFalse.inputSym)
    [leftEraseFalse.inputSym false] := fun h ↦
  absurd ((leftEraseFalse_decidesWithin.outputs_singleTapeTM_iff [true]).1 h 7 (by decide))
    (by decide)

/-- Marked simulation crosses those erased source cells and erases the distant work symbol. -/
example : runCode leftEraseFalse [true, false] 30 =
    some (leftEraseFalse.canonicalSingleTapeTM.haltCfg [leftEraseFalse.canonicalInputSym false]) :=
  rfl

/-- The source erasure gap is handled on every input with the proved class bound. -/
example (x : List Bool) :
    leftEraseFalse.canonicalSingleTapeTM.OutputsWithinTime (x.map leftEraseFalse.canonicalInputSym)
      [leftEraseFalse.canonicalInputSym false] (10 * x.length + 26) := by
  convert leftEraseFalse_decidesWithin.outputsWithinTime_canonicalSingleTapeTM x using 1
  simp only [canonicalTime]
  omega

/-- A genuinely nonhalting source machine: write the current cell and stay in its sole state. -/
def loopTM : SingleTapeTM Bool where
  State := PUnit
  q₀ := PUnit.unit
  tr _ a := (⟨a, none⟩, some PUnit.unit)

private def LoopPhase : Option loopTM.canonicalComputer.State → Prop
  | q => q = some .start ∨ q = some (.run PUnit.unit) ∨ q = some (.mark (some PUnit.unit))

private theorem loopPhase_step {a b : loopTM.canonicalComputer.Cfg}
    (ha : LoopPhase a.state) (h : loopTM.canonicalComputer.TransitionRelation a b) :
    LoopPhase b.state := by
  obtain ⟨q, T⟩ := a
  rcases ha with rfl | rfl | rfl
  all_goals
    rw [TransitionRelation, step_some] at h
    obtain rfl := Option.some_injective _ h
    simp [LoopPhase, loopTM, canonicalComputer]

/-- Marker normalization does not manufacture termination or enter cleanup for a looping source. -/
example (w : List Bool) : ¬loopTM.canonicalComputer.HaltsOn (w.map Canonical.embed) := by
  rintro ⟨b, hb, hhalt⟩
  have hphase : LoopPhase b.state := by
    clear hhalt
    induction hb with
    | refl => exact Or.inl rfl
    | tail _ h ih => exact loopPhase_step ih h
  rw [hhalt] at hphase
  simp [LoopPhase] at hphase

/-- The arbitrary-time class theorem is instantiated, not replaced by a machine-level condition. -/
example : ∃ (Γ : Type) (_ : Inhabited Γ) (_ : Fintype Γ) (ι : Bool → Γ),
    Function.Injective ι ∧ ∃ tm : SingleTapeTM Γ, ∀ w : List Bool,
      tm.OutputsWithinTime (w.map ι) [ι false] (4 * (w.length + 1) + 2 * w.length + 10) :=
  exists_canonicalDecider_of_mem_codeTime (t := fun n ↦ n + 1)
    ⟨Code.constFalse, Code.constFalse_decidesWithin⟩

/-- The polynomial class corollary uses exactly the existing SingleTapeP convention. -/
example : (fun _ ↦ false) ∈ Cslib.Complexity.SingleTapeP :=
  codeTime_polynomial_subset_singleTapeP (Polynomial.X + 1)
    ⟨Code.constFalse, by simpa using Code.constFalse_decidesWithin⟩

#print axioms Cslib.Turing.Universal.exists_canonicalDecider_of_mem_codeTime
#print axioms Cslib.Turing.Universal.codeTime_subset_singleTapeP_of_le_polynomial
#print axioms Cslib.Turing.SingleTapeTM.canonicalComputer_outputsHeadWithinTime
#print axioms Cslib.Turing.SingleTapeTM.Canonical.cleanup_relatesInSteps

end CSLibExtTest.Computability.Machines.Turing.Universal.CodeTimeCanonical
