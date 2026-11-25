/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Framework.GenericGroup.Symbolic

/-!
# Symbolic simulation checks at `q = 7`

Concrete checks at `q = 7` with `enc7 = Equiv.swap 0 3`.
-/

@[expose] public section

namespace CSLibExtTest.Crypto.Framework.GenericGroup.SymbolicTests

open Cslib.Crypto.Framework Cslib.Crypto.Framework.GenericGroup

instance : Fact (1 < 7) := ⟨by decide⟩

def enc7 : Equiv.Perm (ZMod 7) := Equiv.swap 0 3

def twoQuery : GTree (ZMod 7) 3 := .mul 1 2 (.inv 3 (.out 5))

def collideTree : GTree (ZMod 7) 3 := .eqTest 2 1 (.out 1) (.out 0)

def T0 : GTree (ZMod 7) 3 := .eqTest 2 0 (.out 0) (.eqTest 2 1 (.out 1) (.out 2))

theorem twoQuery_numQueries : GTree.numQueries twoQuery = 2 := by decide

theorem twoQuery_compile_run : OracleComp.run (oracleOf enc7) (GTree.compile (dlogInputs enc7 2) twoQuery) = 5 := by decide

theorem twoQuery_answers_length : (GTree.answers (oracleOf enc7) (dlogInputs enc7 2) twoQuery).length = 2 := by decide

theorem affEval_add_spot : affEval (2 : ZMod 7) ((1, 2) + (3, 4)) = affEval 2 (1, 2) + affEval 2 (3, 4) := by decide

theorem affEval_neg_spot : affEval (2 : ZMod 7) (-(1, 2)) = -affEval 2 (1, 2) := by decide

theorem collideTree_symLabels : symLabels (q := 7) collideTree = [(0, 0), (1, 0), (0, 1)] := by decide

theorem collideTree_real_one : GTree.eval (oracleOf enc7) (dlogInputs enc7 1) collideTree = 1 := by decide

theorem collideTree_symbolic : GTree.eval affOracle (dlogForms 7) collideTree = 0 := by decide

theorem collideTree_collision_one : ∃ u ∈ symLabels (q := 7) collideTree, ∃ v ∈ symLabels (q := 7) collideTree, u ≠ v ∧ affEval 1 u = affEval 1 v := by decide

theorem collideTree_agree_two : GTree.eval (oracleOf enc7) (dlogInputs enc7 2) collideTree = GTree.eval affOracle (dlogForms 7) collideTree := by decide

theorem T0_symbolic : GTree.eval affOracle (dlogForms 7) T0 = 2 := by decide

theorem T0_success_iff : ∀ x : ZMod 7, GTree.eval (oracleOf enc7) (dlogInputs enc7 x) T0 = x ↔ x = 0 ∨ x = 1 ∨ x = 2 := by decide

theorem T0_collision_one : ∃ u ∈ symLabels (q := 7) T0, ∃ v ∈ symLabels (q := 7) T0, u ≠ v ∧ affEval 1 u = affEval 1 v := by decide

#print axioms GTree.compile_run
#print axioms GTree.isQueryBounded_compile
#print axioms GTree.length_answers_le
#print axioms GTree.length_pathLabels_le
#print axioms GTree.eval_hom
#print axioms affEval_add
#print axioms affEval_neg
#print axioms length_symLabels_le
#print axioms dlog_eval_eq_sym
#print axioms dlog_success_imp

end CSLibExtTest.Crypto.Framework.GenericGroup.SymbolicTests
