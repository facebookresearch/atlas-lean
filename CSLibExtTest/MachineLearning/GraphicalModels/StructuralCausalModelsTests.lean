/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.StructuralCausalModels
public import Mathlib.Data.Finset.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.FinCases

/-!
# Tests for finite structural causal models

A two-node model on `ℕ` with Boolean noises: `x_0 = [u_0]`, `x_1 = 10 x_0 + [u_1]`.

* At `u = (true, true)` the solution is `(1, 11)`, computed from `solve_isSolution`.
* The structural equations at that noise value have a unique solution.
* `{0}` is parent-closed, so node `0` has the same value at two noise values differing only at
  node `1` (`solve_congr_of_ancestral`).
-/

@[expose] public section

namespace Cslib.MachineLearning.StructuralCausalModelsTests

open Cslib.MachineLearning.GraphicalModels FiniteSCM

def testU : Fin 2 → Type := fun _ => Bool

def testPa : (k : Fin 2) → Finset (Fin k)
  | ⟨0, _⟩ => ∅
  | ⟨1, _⟩ => {0}
  | ⟨n+2, h⟩ => False.elim (by omega)

def testF : (k : Fin 2) → (testPa k → ℕ) → testU k → ℕ
  | ⟨0, _⟩, _, u => match (u : Bool) with | true => 1 | false => 0
  | ⟨1, _⟩, z, u => 10 * z ⟨0, by simp [testPa]⟩ + (match (u : Bool) with | true => 1 | false => 0)
  | ⟨n+2, h⟩, _, _ => False.elim (by omega)

def testM : FiniteSCM ℕ 2 testU := ⟨testPa, testF⟩

def testUVal : (k : Fin 2) → testU k := fun _ => true

def testU2 : (k : Fin 2) → testU k
  | ⟨0, _⟩ => true
  | ⟨1, _⟩ => false
  | ⟨n+2, h⟩ => False.elim (by omega)

def n0 : Fin 2 := ⟨0, by omega⟩
def n1 : Fin 2 := ⟨1, by omega⟩
def testS : Set (Fin 2) := {n0}

example : testM.solve testUVal = ![1, 11] := by
  funext k
  fin_cases k
  · have h0 : testM.solve testUVal n0 = 1 :=
      testM.solve_isSolution testUVal n0
    have hvec : (![1, 11] : Fin 2 → ℕ) n0 = 1 := by simp [n0]
    exact h0.trans hvec.symm
  · have h0 : testM.solve testUVal n0 = 1 :=
      testM.solve_isSolution testUVal n0
    have h1 : testM.solve testUVal n1 = 10 * testM.solve testUVal n0 + 1 :=
      testM.solve_isSolution testUVal n1
    rw [h0] at h1
    have hvec : (![1, 11] : Fin 2 → ℕ) n1 = 11 := by simp [n1]
    exact h1.trans hvec.symm

example : ∃! x, testM.IsSolution testUVal x :=
  testM.existsUnique_isSolution testUVal

example : testM.solve testUVal n0 = testM.solve testU2 n0 := by
  have hS : ∀ k ∈ testS, ∀ j ∈ testM.pa k, Fin.castLE k.2.le j ∈ testS := by
    intro k hk j hj
    simp [testS] at hk
    subst hk
    simp [testM, testPa, n0] at hj
    exact (Finset.notMem_empty j hj).elim
  have hu : ∀ k ∈ testS, testUVal k = testU2 k := by
    intro k hk
    simp [testS] at hk
    subst hk
    rfl
  have hmem : n0 ∈ testS := by simp [testS]
  exact testM.solve_congr_of_ancestral hS hu n0 hmem

end Cslib.MachineLearning.StructuralCausalModelsTests
