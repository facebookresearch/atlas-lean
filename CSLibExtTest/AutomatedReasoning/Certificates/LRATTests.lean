/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# LRAT bridge tests
-/
module

meta import CSLibExt.AutomatedReasoning.Certificates.LRAT

/-!
# LRAT bridge tests

Exercise `Cslib.Logic.PL.CNF.toStd`, `toStd_eval`, and
`not_cnfSat_of_lrat` on concrete formulas via Boolean
evaluation guards and theorem consequences.
-/

open Cslib.Logic.PL

#guard Std.Sat.CNF.eval (fun _ => true)
  (CNF.toStd ([] : CNF)) = true

theorem empty_formula_satisfies :
    CNF.Satisfies (fun _ => true) ([] : CNF) := by
  simp

#guard Std.Sat.CNF.eval (fun _ => true)
  (CNF.toStd ([[]] : CNF)) = false

theorem empty_clause_nsatisfies :
    ¬ CNF.Satisfies (fun _ => true) ([[]] : CNF) := by
  simp

#guard Std.Sat.CNF.eval (fun _ => true)
  (CNF.toStd ([[(0, true)]] : CNF)) = true
#guard Std.Sat.CNF.eval (fun _ => false)
  (CNF.toStd ([[(0, true)]] : CNF)) = false

theorem pos_satisfies :
    CNF.Satisfies (fun _ => true)
      ([[(0, true)]] : CNF) := by
  simp

theorem pos_nsatisfies :
    ¬ CNF.Satisfies (fun _ => false)
      ([[(0, true)]] : CNF) := by
  simp

#guard Std.Sat.CNF.eval (fun _ => false)
  (CNF.toStd ([[(0, false)]] : CNF)) = true
#guard Std.Sat.CNF.eval (fun _ => true)
  (CNF.toStd ([[(0, false)]] : CNF)) = false

theorem neg_satisfies :
    CNF.Satisfies (fun _ => false)
      ([[(0, false)]] : CNF) := by
  simp

theorem neg_nsatisfies :
    ¬ CNF.Satisfies (fun _ => true)
      ([[(0, false)]] : CNF) := by
  simp

#guard Std.Sat.CNF.eval (fun _ => true)
  (CNF.toStd ([[(0, false), (1, true)]] : CNF))
    = true

theorem second_satisfies :
    CNF.Satisfies (fun _ => true)
      ([[(0, false), (1, true)]] : CNF) := by
  simp

#guard Std.Sat.CNF.eval (fun n => n == 0)
  (CNF.toStd ([[(0, false), (1, true)]] : CNF))
    = false

theorem second_nsatisfies :
    ¬ CNF.Satisfies (fun n => n == 0)
      ([[(0, false), (1, true)]] : CNF) := by
  simp

#guard Std.Sat.CNF.eval (fun _ => true)
  (CNF.toStd ([[(0, true)], [(0, false)]] : CNF))
    = false
#guard Std.Sat.CNF.eval (fun _ => false)
  (CNF.toStd ([[(0, true)], [(0, false)]] : CNF))
    = false

theorem p_np_nsatisfies_true :
    ¬ CNF.Satisfies (fun _ => true)
      ([[(0, true)], [(0, false)]] : CNF) := by
  simp

theorem p_np_nsatisfies_false :
    ¬ CNF.Satisfies (fun _ => false)
      ([[(0, true)], [(0, false)]] : CNF) := by
  simp

theorem toStd_eval_mpr_pos :
    Std.Sat.CNF.eval (fun _ => true)
        (CNF.toStd ([[(0, true)]] : CNF)) = true :=
  CNF.toStd_eval.mpr pos_satisfies

theorem toStd_eval_mp_pos :
    CNF.Satisfies (fun _ => true)
      ([[(0, true)]] : CNF) := by
  have hmem : (0, true) ∈
      Std.Sat.CNF.Clause.ofLiterals [(0, true)] := by
    rw [← Std.Sat.CNF.Clause.mem_literals_iff,
      Std.Sat.CNF.Clause.literals_ofLiterals]
    simp
  have hsat : Std.Sat.CNF.Clause.Sat (fun _ => true)
      (Std.Sat.CNF.Clause.ofLiterals [(0, true)]) :=
    Std.Sat.CNF.Clause.sat_of_mem_of_eq hmem rfl
  have heval : Std.Sat.CNF.Clause.eval (fun _ => true)
      (Std.Sat.CNF.Clause.ofLiterals [(0, true)]) = true :=
    (Std.Sat.CNF.Clause.sat_def _ _).mp hsat
  have hstd : Std.Sat.CNF.eval (fun _ => true)
      (CNF.toStd ([[(0, true)]] : CNF)) = true := by
    simp only [CNF.toStd, Std.Sat.CNF.eval_append,
      Std.Sat.CNF.eval_add, Std.Sat.CNF.eval_empty,
      heval, Bool.and_true]
  exact CNF.toStd_eval.mp hstd

theorem sat_no_proof :
    ∀ proof : Array Std.Tactic.BVDecide.LRAT.IntAction,
      Std.Tactic.BVDecide.LRAT.check proof
          (CNF.toStd ([[(0, true)]] : CNF)) ≠
        true := by
  intro proof hcheck
  have hsat : CNFSat ([[(0, true)]] : CNF) :=
    cnfSat_iff_exists_satisfies.mpr
      ⟨fun _ => true, pos_satisfies⟩
  exact CNF.not_cnfSat_of_lrat hcheck hsat

#guard Std.Tactic.BVDecide.LRAT.check
  #[.addEmpty 3 #[1, 2]]
  (CNF.toStd ([[(0, true)], [(0, false)]] : CNF))
    = true
#guard Std.Tactic.BVDecide.LRAT.check
  #[.addEmpty 3 #[1]]
  (CNF.toStd ([[(0, true)], [(0, false)]] : CNF))
    = false

#print axioms toStd_eval_mpr_pos
#print axioms toStd_eval_mp_pos
#print axioms sat_no_proof
