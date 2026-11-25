/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.CookLevin.SATComplete

/-! Tests for the Cook–Levin theorem in its canonical form. -/

namespace MetaMathlibExt.CookLevinSATCompleteTests

open Cslib.CookLevin Cslib.Complexity MetaMathlibExt.ComplexityTheory

/-- SAT is NP-complete in the canonical `NPComplete` packaging. -/
example : NPComplete satDec :=
  npComplete_iff.mpr MetaMathlibExt.cook_levin_SAT_np_complete

/-- Every NP problem reduces to SAT, as the second component states. -/
example (L : DecisionProblem) (hL : L ∈ NP) : PolyManyOneRed L satDec :=
  MetaMathlibExt.cook_levin_SAT_np_complete.2 L hL

/-- The single-clause formula $x_0$ is satisfiable, so its code is in SAT. -/
example : satDec (encodeCNF [[(0, true)]]) = true := by
  rw [Cslib.Complexity.DenseSAT.ToBinary.satDec_encodeCNF]
  exact ⟨fun _ => true, fun C hC => by
    simp only [List.mem_singleton] at hC
    subst hC
    exact ⟨0, true, by simp, rfl⟩⟩

/-- A formula with an empty clause is unsatisfiable, so its code is not in SAT. -/
example : satDec (encodeCNF [[]]) = false := by
  apply Bool.eq_false_iff.mpr
  intro htrue
  rw [Cslib.Complexity.DenseSAT.ToBinary.satDec_encodeCNF] at htrue
  obtain ⟨v, hv⟩ := htrue
  obtain ⟨x, b, hx, -⟩ := hv [] (by simp)
  simp at hx

end MetaMathlibExt.CookLevinSATCompleteTests
