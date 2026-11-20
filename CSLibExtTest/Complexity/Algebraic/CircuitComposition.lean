/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Complexity.Algebraic.CircuitComposition

/-!
# Tests for arithmetic circuit composition and block reindexing

Concrete examples over integers exercising substitution and reindexing.
-/

set_option autoImplicit false

namespace Cslib.Complexity.Algebraic

@[expose] public section

namespace ArithmeticCircuit

private def testD : ArithmeticCircuit ℤ (Fin 2) (Fin 2) where
  size := 1
  gate := fun _ => .add (.input 0) (.input 1)
  output := fun a => if a.val = 0 then .node 0 else .input 1

private def testC : ArithmeticCircuit ℤ (Fin 2) (Fin 1) where
  size := 1
  gate := fun _ => .mul (.input 0) (.input 1)
  output := fun _ => .node 0

private def idCircuit : ArithmeticCircuit ℤ (Fin 2) (Fin 2) where
  size := 0
  gate := fun i => nomatch i
  output := fun a => .input a

private def constD : ArithmeticCircuit ℤ (Fin 2) (Fin 2) where
  size := 0
  gate := fun i => nomatch i
  output := fun a => if a.val = 0 then .constant 7 else .constant 8

private def testC2 : ArithmeticCircuit ℤ (Fin 2) (Fin 1) where
  size := 2
  gate := fun i =>
    if h : i.val = 0 then
      .add (.input 0) (.input 1)
    else
      .mul (.node ⟨0, by have hi := i.isLt; omega⟩) (.input 1)
  output := fun _ => .node 1

example : (testC.subst testD).size = 2 := by
  rw [size_subst]
  decide

example : (testC.subst testD).evaluate (fun i => if i.val = 0 then 2 else 3) 0 = 15 := by
  rw [evaluate_subst]
  simp only [evaluate, testC, testD, ArithmeticOperand.evaluate,
    evaluateNode.eq_1, ArithmeticGate.evaluate]
  decide

example : (testC.subst idCircuit).size = testC.size := by
  rw [size_subst]
  decide

example : (testC.subst idCircuit).evaluate (fun i => if i.val = 0 then 2 else 3) 0 = 6 := by
  rw [evaluate_subst]
  simp only [evaluate, testC, idCircuit, ArithmeticOperand.evaluate,
    evaluateNode.eq_1, ArithmeticGate.evaluate]
  decide

example : testC.evaluate (fun i => if i.val = 0 then 2 else 3) 0 = 6 := by
  simp only [evaluate, testC, ArithmeticOperand.evaluate,
    evaluateNode.eq_1, ArithmeticGate.evaluate]
  decide

example : (testC.subst constD).size = 1 := by
  rw [size_subst]
  decide

example : constD.evaluate (fun i => if i.val = 0 then 2 else 3) 0 = 7 := by
  simp [evaluate, constD, ArithmeticOperand.evaluate]

example : (testC.subst constD).evaluate (fun i => if i.val = 0 then 2 else 3) 0 = 56 := by
  rw [evaluate_subst]
  simp only [evaluate, testC, ArithmeticOperand.evaluate]
  rw [evaluateNode.eq_1]
  simp only [ArithmeticGate.evaluate, ArithmeticOperand.evaluate]
  simp only [constD]
  decide

example : (testC.subst constD).evaluate (fun _ => 0) 0 = 56 := by
  rw [evaluate_subst]
  simp only [evaluate, testC, ArithmeticOperand.evaluate]
  rw [evaluateNode.eq_1]
  simp only [ArithmeticGate.evaluate, ArithmeticOperand.evaluate]
  simp only [constD]
  decide

-- D(2,3) = (5,3); C2 node0 = 5+3 = 8; node1 = 8*3 = 24.
example : (testC2.subst testD).evaluate (fun i => if i.val = 0 then 2 else 3) 0 = 24 := by
  rw [evaluate_subst]
  simp [evaluate, testC2, testD, ArithmeticOperand.evaluate, evaluateNode.eq_1,
    ArithmeticGate.evaluate]

end ArithmeticCircuit

private def testM : Matrix (Fin 4) (Fin 4) ℤ :=
  ![![0, 1, 2, 3], ![4, 5, 6, 7], ![8, 9, 10, 11], ![12, 13, 14, 15]]

example : (finPowSuccEquiv 2 1) 0 = (0, 0) := by decide

example : (finPowSuccEquiv 2 1) 1 = (0, 1) := by decide

example : (finPowSuccEquiv 2 1) 2 = (1, 0) := by decide

example : (finPowSuccEquiv 2 1) 3 = (1, 1) := by decide

example : (matrixFinPowSuccEquiv 2 1 testM) (0, 1) (1, 0) = 6 := by decide

example : (matrixFinPowSuccEquiv 2 1 testM) (0, 1) (1, 0) =
    testM ((finPowSuccEquiv 2 1).symm (0, 1)) ((finPowSuccEquiv 2 1).symm (1, 0)) :=
  matrixFinPowSuccEquiv_apply 2 1 testM (0, 1) (1, 0)

example : (finPowSuccEquiv 2 0) 0 = (0, 0) := by decide

example : (finPowSuccEquiv 2 0) 1 = (1, 0) := by decide

example : Fin (0 ^ (1 + 1)) ≃ Fin 0 × Fin (0 ^ 1) := finPowSuccEquiv 0 1

example : Fin (1 ^ (1 + 1)) ≃ Fin 1 × Fin (1 ^ 1) := finPowSuccEquiv 1 1

example : (finPowSuccEquiv 1 0) 0 = (0, 0) := by decide

end

end Cslib.Complexity.Algebraic
