/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.CyclicStructuralEquations

/-!
# Tests for cyclic structural equations

Concrete solutions and non-solutions of the Boolean systems `x = y, y = x` and `x = ¬y, y = x`.
-/

@[expose] public section

namespace Cslib.MachineLearning.CyclicStructuralEquationsTests

open Cslib.MachineLearning.GraphicalModels StructuralSystem

example : copyCycle.IsSolution ![true, true] := by
  simp only [IsSolution, Fin.forall_fin_two, copyCycle, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  trivial

example : ¬ negCycle.IsSolution ![true, false] := negCycle_not_isSolution _

example : ¬ copyCycle.IsSolution ![true, false] := by
  intro h
  have h0 := h 0
  have h1 := h 1
  simp only [copyCycle, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  simp at h0

end Cslib.MachineLearning.CyclicStructuralEquationsTests
