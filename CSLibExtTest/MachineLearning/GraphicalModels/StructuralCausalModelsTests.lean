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
public import Mathlib.Tactic.NormNum

/-!
# Tests for finite structural causal models

A two-node model on `ℕ` with Boolean noises: `x_0 = [u_0]`, `x_1 = 10 x_0 + [u_1]`.

* At `u = (true, true)` the solution is `(1, 11)`, computed from `solve_isSolution`.
* The structural equations at that noise value have a unique solution.
* `{0}` is parent-closed, so node `0` has the same value at two noise values differing only at
  node `1` (`solve_congr_of_ancestral`).

A two-node model on `Bool` with independent Boolean noises (`P(u_0) = 1/4`, `P(u_1) = 1/3`),
`x_0 = u_0`, `x_1 = x_0 xor u_1`:

* the induced Bayesian network's table at node `1` for parent value `true` gives `false`
  probability `1/3`;
* the induced law of `(true, false)` is `1/12`, computed through `inducedLaw_eq_joint`.

A two-node Bayesian network on `Bool` (`P(X_0) = 1/4`, `P(X_1 | X_0 = true) = 2/3`,
`P(X_1 | X_0 = false) = 1/2`) and its response-function SCM:

* the identity response of node `1` has weight `2/3 · 1/2 = 1/3`;
* the realization's law of `(true, true)` is `1/6`, through `responseSCM_inducedLaw`.
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

namespace InducedBayesNet

open Convexity

/-- Parents in the test model: node 0 has none, node 1 has parent 0. -/
def testPa : (k : Fin 2) → Finset (Fin k.val)
  | ⟨0, h0⟩ => ∅
  | ⟨1, h1⟩ => {⟨0, Nat.zero_lt_succ 0⟩}
  | ⟨n + 2, h⟩ => False.elim (by omega)

/-- The parent of node 1 as an element of its parent type. -/
def testJ0 : ↥(testPa 1) := ⟨⟨0, Nat.zero_lt_succ 0⟩, by decide⟩

/-- Structural functions: node 0 copies its noise, node 1 xors its parent with its noise. -/
def testF : (k : Fin 2) → (testPa k → Bool) → Bool → Bool
  | ⟨0, h0⟩, _, u => u
  | ⟨1, h1⟩, z, u => xor (z ⟨⟨0, Nat.zero_lt_succ 0⟩, Finset.mem_singleton_self _⟩) u
  | ⟨n + 2, h⟩, _, _ => False.elim (by omega)

/-- The two-node test model. -/
def testM : FiniteSCM Bool 2 (fun _ => Bool) where
  pa := testPa
  f := testF

/-- Noise laws: `true` has probability `1/4` at node 0 and `1/3` at node 1. -/
noncomputable def testMu : (k : Fin 2) → StdSimplex ℝ Bool
  | ⟨0, h0⟩ => StdSimplex.duple true false (s := 1/4) (t := 3/4)
      (by norm_num) (by norm_num) (by norm_num)
  | ⟨1, h1⟩ => StdSimplex.duple true false (s := 1/3) (t := 2/3)
      (by norm_num) (by norm_num) (by norm_num)
  | ⟨n + 2, h⟩ => False.elim (by omega)

/-- Node 0 copies its noise. -/
theorem testF_zero (z : testPa 0 → Bool) (v : Bool) : testF 0 z v = v := rfl

/-- Node 1 xors its parent's value with its noise. -/
theorem testF_one (z : testPa 1 → Bool) (v : Bool) :
    testF 1 z v = xor (z testJ0) v := rfl

/-- Noise weights at node 0. -/
theorem testMu_zero_true : (testMu 0).weights true = 1/4 := by
  have hmu : testMu 0 = StdSimplex.duple true false (s := 1/4) (t := 3/4)
      (by norm_num) (by norm_num) (by norm_num) := rfl
  rw [hmu, StdSimplex.weights_duple, Finsupp.add_apply, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne (show (true : Bool) ≠ false by decide), add_zero]

/-- Noise weights at node 1. -/
theorem testMu_one_true : (testMu 1).weights true = 1/3 := by
  have hmu : testMu 1 = StdSimplex.duple true false (s := 1/3) (t := 2/3)
      (by norm_num) (by norm_num) (by norm_num) := rfl
  rw [hmu, StdSimplex.weights_duple, Finsupp.add_apply, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne (show (true : Bool) ≠ false by decide), add_zero]

/-- The table at node 1 for parent value `true` gives `false` probability `1/3`. -/
theorem test_cpt1 (z : testPa 1 → Bool) (hz : z testJ0 = true) :
    ((testM.inducedBayesNet testMu).cpt 1 z).weights false = 1/3 := by
  have hmap : ((testM.inducedBayesNet testMu).cpt 1 z)
      = (testMu 1).map (testF 1 z) := rfl
  rw [hmap, StdSimplex.weights_map, Finsupp.mapDomain_fintype, Finsupp.coe_finsetSum,
    Finset.sum_apply, Fintype.sum_bool]
  simp only [testF_one]
  rw [hz]
  have e1 : xor true true = false := rfl
  have e2 : xor true false = true := rfl
  rw [e1, e2, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne (show (false : Bool) ≠ true by decide),
    testMu_one_true, add_zero]

example (z : testPa 1 → Bool) (hz : z testJ0 = true) :
    ((testM.inducedBayesNet testMu).cpt 1 z).weights false = 1/3 :=
  test_cpt1 z hz

example : testM.inducedLaw testMu ![true, false] = 1/12 := by
  have x0 : ![true, false] (0 : Fin 2) = true := by simp
  have x1 : ![true, false] (1 : Fin 2) = false := by simp
  rw [inducedLaw_eq_joint, BayesNet.joint_eq_prod, Fin.prod_univ_two, x0, x1]
  have hpar : ![true, false] (Fin.castLE (1 : Fin 2).2.le testJ0.val) = true := by
    have hcast : Fin.castLE (1 : Fin 2).2.le testJ0.val = 0 := by decide
    rw [hcast]
    exact x0
  have f1 : ((testM.inducedBayesNet testMu).cpt 1
      (fun j => ![true, false] (Fin.castLE (1 : Fin 2).2.le j))).weights false = 1/3 :=
    test_cpt1 _ hpar
  have f0 : ((testM.inducedBayesNet testMu).cpt 0
      (fun j => ![true, false] (Fin.castLE (0 : Fin 2).2.le j))).weights true = 1/4 := by
    have hmap : ((testM.inducedBayesNet testMu).cpt 0
        (fun j => ![true, false] (Fin.castLE (0 : Fin 2).2.le j)))
        = (testMu 0).map (testF 0
          (fun j => ![true, false] (Fin.castLE (0 : Fin 2).2.le j))) := rfl
    rw [hmap, StdSimplex.weights_map, Finsupp.mapDomain_fintype, Finsupp.coe_finsetSum,
      Finset.sum_apply, Fintype.sum_bool]
    simp only [testF_zero]
    rw [Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne (show (true : Bool) ≠ false by decide),
      testMu_zero_true, add_zero]
  rw [f0, f1]
  norm_num

end InducedBayesNet

namespace ResponseRealization

open Convexity BayesNet

/-- Distribution of node 0: `P(true) = 1/4`. -/
noncomputable def testDist0 : StdSimplex ℝ Bool where
  weights := Finsupp.equivFunOnFinite.symm
    (fun b => match b with | true => (1/4 : ℝ) | false => (3/4 : ℝ))
  nonneg := fun b => by
    have h : (Finsupp.equivFunOnFinite.symm
        (fun b : Bool => match b with | true => (1/4 : ℝ) | false => (3/4 : ℝ))) b
        = (match b with | true => (1/4 : ℝ) | false => (3/4 : ℝ)) := rfl
    rw [h]
    cases b <;> norm_num
  total := by
    rw [Finsupp.sum_fintype _ _ fun _ => rfl]
    have h : ∀ b : Bool, (Finsupp.equivFunOnFinite.symm
        (fun b : Bool => match b with | true => (1/4 : ℝ) | false => (3/4 : ℝ))) b
        = (match b with | true => (1/4 : ℝ) | false => (3/4 : ℝ)) := fun _ => rfl
    simp only [h]
    have huniv : (Finset.univ : Finset Bool) = {false, true} := by decide
    rw [huniv, Finset.sum_insert (by decide), Finset.sum_singleton]
    norm_num

/-- Distribution of node 1 given parent `true`: `P(true) = 2/3`. -/
noncomputable def testDistTrue : StdSimplex ℝ Bool where
  weights := Finsupp.equivFunOnFinite.symm
    (fun b => match b with | true => (2/3 : ℝ) | false => (1/3 : ℝ))
  nonneg := fun b => by
    have h : (Finsupp.equivFunOnFinite.symm
        (fun b : Bool => match b with | true => (2/3 : ℝ) | false => (1/3 : ℝ))) b
        = (match b with | true => (2/3 : ℝ) | false => (1/3 : ℝ)) := rfl
    rw [h]
    cases b <;> norm_num
  total := by
    rw [Finsupp.sum_fintype _ _ fun _ => rfl]
    have h : ∀ b : Bool, (Finsupp.equivFunOnFinite.symm
        (fun b : Bool => match b with | true => (2/3 : ℝ) | false => (1/3 : ℝ))) b
        = (match b with | true => (2/3 : ℝ) | false => (1/3 : ℝ)) := fun _ => rfl
    simp only [h]
    have huniv : (Finset.univ : Finset Bool) = {false, true} := by decide
    rw [huniv, Finset.sum_insert (by decide), Finset.sum_singleton]
    norm_num

/-- Distribution of node 1 given parent `false`: `P(true) = 1/2`. -/
noncomputable def testDistFalse : StdSimplex ℝ Bool where
  weights := Finsupp.equivFunOnFinite.symm
    (fun b => match b with | true => (1/2 : ℝ) | false => (1/2 : ℝ))
  nonneg := fun b => by
    have h : (Finsupp.equivFunOnFinite.symm
        (fun b : Bool => match b with | true => (1/2 : ℝ) | false => (1/2 : ℝ))) b
        = (match b with | true => (1/2 : ℝ) | false => (1/2 : ℝ)) := rfl
    rw [h]
    cases b <;> norm_num
  total := by
    rw [Finsupp.sum_fintype _ _ fun _ => rfl]
    have h : ∀ b : Bool, (Finsupp.equivFunOnFinite.symm
        (fun b : Bool => match b with | true => (1/2 : ℝ) | false => (1/2 : ℝ))) b
        = (match b with | true => (1/2 : ℝ) | false => (1/2 : ℝ)) := fun _ => rfl
    simp only [h]
    have huniv : (Finset.univ : Finset Bool) = {false, true} := by decide
    rw [huniv, Finset.sum_insert (by decide), Finset.sum_singleton]
    norm_num

/-- Two-node network: node 0 has no parents, node 1 has parent 0. -/
noncomputable def testNet : BayesNet Bool 2 where
  pa := fun _ => Finset.univ
  cpt := fun k =>
    match k with
    | ⟨0, _⟩ => fun _ => testDist0
    | ⟨1, _⟩ => fun z => match z ⟨0, Finset.mem_univ 0⟩ with
      | true => testDistTrue
      | false => testDistFalse
    | ⟨n+2, h⟩ => fun _ => absurd h (by omega)

/-- The identity response of node 1 has weight `2/3 * 1/2 = 1/3`. -/
example : testNet.responseWeight ⟨1, by decide⟩
    (fun z => z ⟨0, Finset.mem_univ 0⟩) = (1/3 : ℝ) := by
  simp only [responseWeight]
  have huniv : (Finset.univ : Finset (testNet.pa ⟨1, by decide⟩ → Bool))
      = {fun _ => true, fun _ => false} := by decide
  rw [huniv, Finset.prod_insert (by decide), Finset.prod_singleton]
  show (2/3 : ℝ) * (1/2) = 1/3
  norm_num

/-- The induced law at `![true, true]` is `1/4 * 2/3 = 1/6`. -/
example : testNet.responseSCM.inducedLaw testNet.responseLaw ![true, true] = (1/6 : ℝ) := by
  rw [responseSCM_inducedLaw, joint_eq_prod]
  have huniv2 : (Finset.univ : Finset (Fin 2))
      = {⟨0, by decide⟩, ⟨1, by decide⟩} := by decide
  rw [huniv2, Finset.prod_insert (by decide), Finset.prod_singleton]
  have hx0 : (![true, true] : Fin 2 → Bool) ⟨0, by decide⟩ = true := by simp
  have hx1 : (![true, true] : Fin 2 → Bool) ⟨1, by decide⟩ = true := by simp
  rw [hx0, hx1]
  show (1/4 : ℝ) * (2/3) = 1/6
  norm_num

end ResponseRealization

end Cslib.MachineLearning.StructuralCausalModelsTests
