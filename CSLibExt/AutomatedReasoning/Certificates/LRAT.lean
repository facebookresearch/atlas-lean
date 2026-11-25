/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Atlas CNF to Std CNF/LRAT bridge
-/
module

public import CSLibExt.Logics.Propositional.CNF.Semantics
public import Std.Sat.CNF
public import Std.Tactic.BVDecide.LRAT.Checker

/-!
# Atlas CNF to Std CNF/LRAT bridge

Translate Atlas `Cslib.Logic.LegacyPL.CNF` to core `Std.Sat.CNF Nat`
and transfer native LRAT unsat certificates across the bridge.
-/

@[expose] public section

namespace Cslib.Logic.LegacyPL

namespace CNF

/-- Translate Atlas CNF to core `Std.Sat.CNF Nat`.

Atoms are unchanged Nat variables, each literal's polarity
and each clause/formula list structure are preserved via
`Std.Sat.CNF.Clause.ofLiterals`. -/
def toStd : CNF → Std.Sat.CNF Nat
  | [] => .empty
  | clause :: rest =>
    (Std.Sat.CNF.empty.add
      (Std.Sat.CNF.Clause.ofLiterals clause)) ++
      toStd rest

private theorem clause_sat_ofLiterals
    {a : Nat → Bool} {clause : CNFClause} :
    Std.Sat.CNF.Clause.Sat a
        (Std.Sat.CNF.Clause.ofLiterals clause) ↔
      CNFClause.Satisfies a clause := by
  rw [Std.Sat.CNF.Clause.sat_iff_exists_mem_eq]
  rw [CNFClause.satisfies_def]
  constructor
  · rintro ⟨lit, hmem, heq⟩
    rw [← Std.Sat.CNF.Clause.mem_literals_iff] at hmem
    rw [Std.Sat.CNF.Clause.literals_ofLiterals] at hmem
    exact ⟨lit, hmem, heq⟩
  · rintro ⟨lit, hmem, heq⟩
    refine ⟨lit, ?_, heq⟩
    rw [← Std.Sat.CNF.Clause.mem_literals_iff]
    rw [Std.Sat.CNF.Clause.literals_ofLiterals]
    exact hmem

private theorem toStd_nil : toStd [] = .empty := rfl

private theorem toStd_cons
    (clause : CNFClause) (rest : CNF) :
    toStd (clause :: rest) =
      (Std.Sat.CNF.empty.add
        (Std.Sat.CNF.Clause.ofLiterals clause)) ++
        toStd rest := rfl

private theorem toStd_append (φ ψ : CNF) :
    toStd (φ ++ ψ) = toStd φ ++ toStd ψ := by
  induction φ with
  | nil => simp [toStd]
  | cons head tail ih =>
    simp [toStd, ih, Std.Sat.CNF.append_assoc]

/-- Core evaluation of the translated formula is true exactly
when the same assignment satisfies the source Atlas formula.

Atoms are unchanged Nat variables and polarity is preserved;
covers empty clause (false), empty formula (true), and
cons/append structure. -/
theorem toStd_eval {v : Nat → Bool} {φ : CNF} :
    Std.Sat.CNF.eval v (toStd φ) = true ↔
      φ.Satisfies v := by
  induction φ with
  | nil => simp [toStd]
  | cons head tail ih =>
    rw [toStd_cons]
    rw [Std.Sat.CNF.eval_append]
    have hhead :
        Std.Sat.CNF.eval v
            (Std.Sat.CNF.empty.add
              (Std.Sat.CNF.Clause.ofLiterals head)) =
          true ↔
          CNFClause.Satisfies v head := by
      simp only [Std.Sat.CNF.eval_add,
        Std.Sat.CNF.eval_empty, Bool.and_true]
      rw [← Std.Sat.CNF.Clause.sat_def]
      exact clause_sat_ofLiterals
    rw [Bool.and_eq_true]
    rw [hhead, ih]
    exact CNF.satisfies_cons.symm

/-- If the native BVDecide LRAT checker accepts the supplied
proof for the translated source formula, the source formula
is not `CNFSat`.

This is only imported checker soundness (`check_sound`)
transferred across the evaluation bridge; atoms are unchanged
Nat variables and polarity is preserved. -/
theorem not_cnfSat_of_lrat
    {φ : CNF}
    {proof : Array Std.Tactic.BVDecide.LRAT.IntAction} :
    Std.Tactic.BVDecide.LRAT.check proof (toStd φ)
      = true →
      ¬ CNFSat φ := by
  intro hcheck hsat
  have hunsat :=
    Std.Tactic.BVDecide.LRAT.check_sound proof
      (toStd φ) hcheck
  rw [Std.Sat.CNF.unsat_def] at hunsat
  obtain ⟨v, hv⟩ := cnfSat_iff_exists_satisfies.mp hsat
  have heval := (toStd_eval (v := v) (φ := φ)).mpr hv
  have hfalse := hunsat v
  rw [heval] at hfalse
  cases hfalse

end CNF

end Cslib.Logic.LegacyPL

#print axioms Cslib.Logic.LegacyPL.CNF.toStd
#print axioms Cslib.Logic.LegacyPL.CNF.clause_sat_ofLiterals
#print axioms Cslib.Logic.LegacyPL.CNF.toStd_nil
#print axioms Cslib.Logic.LegacyPL.CNF.toStd_cons
#print axioms Cslib.Logic.LegacyPL.CNF.toStd_append
#print axioms Cslib.Logic.LegacyPL.CNF.toStd_eval
#print axioms Cslib.Logic.LegacyPL.CNF.not_cnfSat_of_lrat
