/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Computability.Complexity.SpaceInclusions
import CSLibExtTest.Computability.Machines.Turing.MultiTape.TimeSpaceTests

/-!
# Same-machine consumers of the polynomial-space inclusion

The existing first-bit decider accepts and rejects actual raw inputs. Its new
exponential bound is used to read the output at that bound, not just to prove
membership in a class. A constant-output decider also covers empty acceptance.
A stationary zero-space loop demonstrates why halting cannot be dropped.
-/

open _root_.Turing Cslib.Turing.MultiTapeTM
open CSLibExtTest.Computability.Machines.Turing.MultiTape
open MetaMathlibExt.Complexity.KeyTheorems.PSPACESubsetEXP

private theorem firstBit_exponential :
    ∃ D A B : ℕ, ∀ w : List Bool,
      firstBitTM.RunsInTime w (A * 2 ^ (w.length ^ D) + B) ∧
      (firstBitTM.runFrom (firstBitTM.initCfg w)
        (A * 2 ^ (w.length ^ D) + B)).output =
          [w.head? == some true] := by
  have hs : SpaceBoundedBy firstBitTM (fun n => 0 * n ^ 0 + 0) := by
    simpa using firstBitTM_spaceBoundedBy
  obtain ⟨D, A, B, ht⟩ :=
    hs.exists_exponential_timeBoundedBy firstBitTM_decides
  refine ⟨D, A, B, fun w => ⟨ht w, ?_⟩⟩
  exact (computes_iff_output_of_runsInTime (ht w)).mp
    ⟨1, (firstBitTM_runFrom_one w).1, (firstBitTM_runFrom_one w).2⟩

private theorem firstBit_boundary_outputs :
    ∃ D A B : ℕ,
      (firstBitTM.runFrom (firstBitTM.initCfg [])
        (A * 2 ^ (0 ^ D) + B)).output = [false] ∧
      (firstBitTM.runFrom (firstBitTM.initCfg [true])
        (A * 2 ^ (1 ^ D) + B)).output = [true] ∧
      (firstBitTM.runFrom (firstBitTM.initCfg [false, true])
        (A * 2 ^ (2 ^ D) + B)).output = [false] := by
  obtain ⟨D, A, B, h⟩ := firstBit_exponential
  exact ⟨D, A, B, (h []).2, (h [true]).2, (h [false, true]).2⟩

private theorem firstBit_nonzero_polynomial :
    ∃ D A B : ℕ,
      TimeBoundedBy firstBitTM (fun n => A * 2 ^ (n ^ D) + B) := by
  have hs : SpaceBoundedBy firstBitTM (fun n => 2 * n ^ 3 + 1) :=
    firstBitTM_spaceBoundedBy.mono fun _ => Nat.zero_le _
  exact hs.exists_exponential_timeBoundedBy firstBitTM_decides

private def firstBitProblem (w : List Bool) : Bool := w.head? == some true

private theorem firstBit_pspace :
    firstBitProblem ∈ Cslib.Complexity.Classes.PSPACE := by
  apply Set.mem_iUnion.mpr
  refine ⟨0, mem_DSPACE_iff.mpr
    ⟨0, 0, 0, Unit, inferInstance, firstBitTM, ?_, ?_,
      _, firstBitTM_timeBoundedBy⟩⟩
  · have he : Cslib.Complexity.Classes.langOf firstBitProblem =
        startsWithTrue := by
      ext w
      simp [Cslib.Complexity.Classes.langOf, firstBitProblem, startsWithTrue]
    rw [he]
    exact firstBitTM_decides
  · simpa using firstBitTM_spaceBoundedBy

private theorem firstBit_exp :
    firstBitProblem ∈ Cslib.Complexity.Classes.EXP :=
  pspace_subset_exp firstBit_pspace

private def constantTM (b : Bool) : MultiTapeTM 0 Bool Unit :=
  MultiTapeTM.ofTr () fun _ _ _ => ⟨0, Fin.elim0, some b, none⟩

private theorem constant_computes (b : Bool) (w : List Bool) :
    (constantTM b).Computes w [b] := by
  refine ⟨1, ?_, ?_⟩ <;>
    simp [constantTM, runFrom_ofTr, stepWith, Cfg.Halted]

private theorem constant_decides (b : Bool) :
    Decides (constantTM b) {w | (fun _ : List Bool => b) w = true} := by
  intro w
  convert constant_computes b w using 1
  cases b <;> simp [MultiTapeTM.indicator]

private theorem constant_exponential (b : Bool) :
    ∃ D A B : ℕ, ∀ w : List Bool,
      (constantTM b).RunsInTime w (A * 2 ^ (w.length ^ D) + B) ∧
      ((constantTM b).runFrom ((constantTM b).initCfg w)
        (A * 2 ^ (w.length ^ D) + B)).output = [b] := by
  have hs : SpaceBoundedBy (constantTM b) (fun n => 0 * n ^ 0 + 0) :=
    fun w => MultiTapeNTM.runsInSpace_zero_tapes _ w _
  obtain ⟨D, A, B, ht⟩ := hs.exists_exponential_timeBoundedBy
    (constant_decides b)
  exact ⟨D, A, B, fun w => ⟨ht w,
    (computes_iff_output_of_runsInTime (ht w)).mp (constant_computes b w)⟩⟩

private theorem empty_acceptance :
    ∃ D A B : ℕ,
      ((constantTM true).runFrom ((constantTM true).initCfg [])
        (A * 2 ^ (0 ^ D) + B)).output = [true] := by
  obtain ⟨D, A, B, h⟩ := constant_exponential true
  exact ⟨D, A, B, (h []).2⟩

private def stationaryTM : MultiTapeTM 0 Bool Unit :=
  MultiTapeTM.ofTr () fun _ _ _ => ⟨0, Fin.elim0, none, some ()⟩

private theorem stationary_run (w : List Bool) (t : ℕ) :
    stationaryTM.runFrom (stationaryTM.initCfg w) t =
      stationaryTM.initCfg w := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ, ih]
    apply Cfg.ext_zero_tapes <;>
      simp [stationaryTM, step_ofTr, stepWith, Action.apply]

private theorem stationary_space (w : List Bool) :
    stationaryTM.RunsInSpace w 0 :=
  MultiTapeNTM.runsInSpace_zero_tapes _ w _

private theorem stationary_no_time (w : List Bool) (t : ℕ) :
    ¬stationaryTM.RunsInTime w t := by
  intro ht
  have hh := halted_runFrom_of_runsInTime ht
  rw [stationary_run] at hh
  change (some () : Option Unit) = none at hh
  contradiction

private theorem stationary_not_decider (L : Set (List Bool)) :
    ¬Decides stationaryTM L := by
  intro hd
  obtain ⟨t, ht, _⟩ := hd []
  exact stationary_no_time [] t (MultiTapeTM.runsInTime_of_halted ht)

example : (0 : ℕ) ^ 0 = 1 := by decide
example : (1 : ℕ) ^ 0 = 1 := by decide
example : (0 : ℕ) ^ 2 = 0 := by decide

#print axioms pspace_subset_exp
#print axioms SpaceBoundedBy.exists_exponential_timeBoundedBy
