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

Surgery on the Boolean xor model above (`x_0 = u_0`, `x_1 = x_0 xor u_1`, `P(u_0) = 1/4`,
`P(u_1) = 1/3`):

* after `do(X_0 = true)` the law of `(true, false)` is `1/3` and of `(false, false)` is `0`;
* after surgery on the set `{0}` with value `true` the law of `(true, false)` is `1/3`.

Counterfactuals in the same xor model, with evidence `X_1 = false` and `do(X_0 = false)`:

* the evidence has probability `7/12`;
* `P(X_1 = true had X_0 been false | X_1 = false) = 1/7`, while the interventional probability
  `P(X_1 = true | do(X_0 = false))` is `1/3`: sharing the noise between the factual and the
  counterfactual world matters.
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

namespace Surgery

open Convexity

/-- A nonzero node of `Fin 2` has nonzero value. -/
theorem val_ne_zero_of_ne_zero {k : Fin 2} (h : k ≠ 0) : k.val ≠ 0 := by
  intro hv
  apply h
  rw [Fin.ext_iff]
  simpa [Fin.val_zero] using hv

/-- Parents for the xor test model: node 0 has no parents, node 1 has parent 0. -/
def paXor : (k : Fin 2) → Finset (Fin k) := fun k =>
  if h : k = 0 then ∅ else {⟨0, Nat.pos_of_ne_zero (val_ne_zero_of_ne_zero h)⟩}

/-- Structural functions for the xor test model: node 0 copies its noise, node 1 xors the
value of its parent with its noise. -/
def fXor : (k : Fin 2) → (paXor k → Bool) → Bool → Bool := fun k z u =>
  if h : k = 0 then u
  else
    have hk0 : k.val ≠ 0 := val_ne_zero_of_ne_zero h
    have hmem : (⟨0, Nat.pos_of_ne_zero hk0⟩ : Fin k.val) ∈ paXor k := by
      simp only [paXor, dite_eq_right h]
      exact Finset.mem_singleton_self _
    xor (z ⟨⟨0, Nat.pos_of_ne_zero hk0⟩, hmem⟩) u

/-- The two-node xor test model. -/
def M : FiniteSCM Bool 2 (fun _ => Bool) where
  pa := paXor
  f := fXor

/-- Noise law at node 0: `true` with probability `1/4`. -/
noncomputable def μ0 : StdSimplex ℝ Bool :=
  StdSimplex.duple true false (s := 1 / 4) (t := 3 / 4) (by norm_num) (by norm_num)
    (by norm_num)

/-- Noise law at node 1: `true` with probability `1/3`. -/
noncomputable def μ1 : StdSimplex ℝ Bool :=
  StdSimplex.duple true false (s := 1 / 3) (t := 2 / 3) (by norm_num) (by norm_num)
    (by norm_num)

/-- Noise laws of the xor test model. -/
noncomputable def μ : (k : Fin 2) → StdSimplex ℝ Bool := ![μ0, μ1]

theorem μ0_true : μ0.weights true = 1 / 4 := by
  simp [μ0, StdSimplex.weights_duple]

theorem μ1_true : μ1.weights true = 1 / 3 := by
  simp [μ1, StdSimplex.weights_duple]

theorem μ_one_true : (μ 1).weights true = 1 / 3 := by
  have hμ : μ 1 = μ1 := by simp [μ]
  rw [hμ]
  exact μ1_true

theorem fXor_zero (z : paXor 0 → Bool) (u : Bool) : fXor 0 z u = u := by
  simp [fXor]

theorem fXor_one (g : paXor 1 → Bool) (hg : ∀ i, g i = true) (v : Bool) :
    fXor 1 g v = xor true v := by
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  simp only [fXor, dite_eq_right h10]
  congr 1
  exact hg _

/-- The test assignment `![true, false]` is `true` at any index of value `0`. -/
theorem x_castLE_zero (m : ℕ) (h : m ≤ 2) (j : Fin m) (hj : j.val = 0) :
    (![true, false] : Fin 2 → Bool) (Fin.castLE h j) = true := by
  have hceq : Fin.castLE h j = (0 : Fin 2) := by simp [Fin.ext_iff, Fin.val_castLE, hj]
  rw [hceq]
  simp

/-- The node-1 push-forward factor at `false` is `1/3` whenever the parent value is `true`. -/
theorem map1_weights (g : paXor 1 → Bool) (hg : ∀ i, g i = true) :
    ((μ 1).map (fXor 1 g)).weights false = 1 / 3 := by
  rw [StdSimplex.weights_map, Finsupp.mapDomain_fintype, Finsupp.coe_finsetSum,
    Finset.sum_apply]
  simp only [Finsupp.single_apply]
  have hfib : ∀ v : Bool, fXor 1 g v = xor true v := fun v => fXor_one g hg v
  simp only [hfib]
  have hcond : ∀ v : Bool, (if xor true v = false then (μ 1).weights v else (0 : ℝ))
      = (if v = true then (μ 1).weights v else 0) := by
    intro v
    cases v <;> rfl
  simp only [hcond]
  rw [Fintype.sum_bool]
  simp [μ_one_true]

example : (M.doNode 0 true).inducedLaw μ ![true, false] = 1 / 3 := by
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  have hx1 : (![true, false] : Fin 2 → Bool) 1 = false := by simp
  have hfac0 : ∀ z : ((M.inducedBayesNet μ).intervene 0 true).pa 0 → Bool,
      (((M.inducedBayesNet μ).intervene 0 true).cpt 0 z).weights
        ((![true, false] : Fin 2 → Bool) 0) = 1 := by
    intro z
    have hcpt : ((M.inducedBayesNet μ).intervene 0 true).cpt 0 z
        = StdSimplex.single true := by
      simp [BayesNet.intervene]
    rw [hcpt]
    have hx0 : (![true, false] : Fin 2 → Bool) 0 = true := by simp
    rw [hx0]
    simp [StdSimplex.weights_single]
  rw [FiniteSCM.inducedLaw_doNode, BayesNet.joint_eq_prod, Fin.prod_univ_two, hfac0, hx1]
  rw [one_mul]
  simp only [BayesNet.intervene, dite_eq_right h10, FiniteSCM.inducedBayesNet, M]
  refine map1_weights _ ?_
  intro i
  have hj0 : i.1.val = 0 := by
    have hlt := i.1.isLt
    simp at hlt
    omega
  exact x_castLE_zero _ _ _ hj0

example : (M.doNode 0 true).inducedLaw μ ![false, false] = 0 := by
  have hfac0 : ∀ z : ((M.inducedBayesNet μ).intervene 0 true).pa 0 → Bool,
      (((M.inducedBayesNet μ).intervene 0 true).cpt 0 z).weights
        ((![false, false] : Fin 2 → Bool) 0) = 0 := by
    intro z
    have hcpt : ((M.inducedBayesNet μ).intervene 0 true).cpt 0 z
        = StdSimplex.single true := by
      simp [BayesNet.intervene]
    rw [hcpt]
    have hx0 : (![false, false] : Fin 2 → Bool) 0 = false := by simp
    rw [hx0]
    simp [StdSimplex.weights_single]
  rw [FiniteSCM.inducedLaw_doNode, BayesNet.joint_eq_prod, Fin.prod_univ_two, hfac0,
    zero_mul]

example : (M.doSet {0} ![true, true]).inducedLaw μ ![true, false] = 1 / 3 := by
  have h1W : (1 : Fin 2) ∉ ({0} : Finset (Fin 2)) := by simp
  have h0W : (0 : Fin 2) ∈ ({0} : Finset (Fin 2)) := by simp
  have hx1 : (![true, false] : Fin 2 → Bool) 1 = false := by simp
  have hfac0 : ∀ z : ((M.inducedBayesNet μ).mutilateSet {0} ![true, true]).pa 0 → Bool,
      (((M.inducedBayesNet μ).mutilateSet {0} ![true, true]).cpt 0 z).weights
        ((![true, false] : Fin 2 → Bool) 0) = 1 := by
    intro z
    have hcpt : ((M.inducedBayesNet μ).mutilateSet {0} ![true, true]).cpt 0 z
        = StdSimplex.single ((![true, true] : Fin 2 → Bool) 0) := by
      simp [BayesNet.mutilateSet, h0W]
    rw [hcpt]
    have hw0 : (![true, true] : Fin 2 → Bool) 0 = true := by simp
    rw [hw0]
    have hx0 : (![true, false] : Fin 2 → Bool) 0 = true := by simp
    rw [hx0]
    simp [StdSimplex.weights_single]
  rw [FiniteSCM.inducedLaw_doSet, BayesNet.joint_eq_prod, Fin.prod_univ_two, hfac0, hx1]
  rw [one_mul]
  simp only [BayesNet.mutilateSet, dite_eq_right h1W, FiniteSCM.inducedBayesNet, M]
  refine map1_weights _ ?_
  intro i
  have hj0 : i.1.val = 0 := by
    have hlt := i.1.isLt
    simp at hlt
    omega
  exact x_castLE_zero _ _ _ hj0

end Surgery

namespace Counterfactuals

open Convexity

/-- Test model parents: node 0 has no parents; node 1 has parent 0. -/
def xorTestPa (k : Fin 2) : Finset (Fin k) :=
  if k.val = 0 then ∅ else Finset.univ

/-- Test model: node 0 relays its noise; node 1 xors parent 0 with its noise. -/
def xorTestModel : FiniteSCM Bool 2 (fun _ => Bool) where
  pa := xorTestPa
  f k z u := if h : k.val = 0 then u
    else xor (z ⟨⟨0, by omega⟩, by simp [xorTestPa, h]⟩) u

/-- Test noise law giving `true` probability `1/4`. -/
noncomputable def xorTestMu14 : StdSimplex ℝ Bool where
  weights :=
    Finsupp.onFinset Finset.univ (fun b => if b then (1/4 : ℝ) else 3/4)
      (fun a _ => Finset.mem_univ a)
  nonneg := by
    rw [Finsupp.le_def]
    intro b
    cases b
    · show (0 : ℝ) ≤ 3 / 4
      norm_num
    · show (0 : ℝ) ≤ 1 / 4
      norm_num
  total := by
    rw [Finsupp.sum_fintype _ _ fun _ => rfl]
    rw [Fintype.sum_bool]
    show (1 / 4 : ℝ) + 3 / 4 = 1
    norm_num

/-- Test noise law giving `true` probability `1/3`. -/
noncomputable def xorTestMu13 : StdSimplex ℝ Bool where
  weights :=
    Finsupp.onFinset Finset.univ (fun b => if b then (1/3 : ℝ) else 2/3)
      (fun a _ => Finset.mem_univ a)
  nonneg := by
    rw [Finsupp.le_def]
    intro b
    cases b
    · show (0 : ℝ) ≤ 2 / 3
      norm_num
    · show (0 : ℝ) ≤ 1 / 3
      norm_num
  total := by
    rw [Finsupp.sum_fintype _ _ fun _ => rfl]
    rw [Fintype.sum_bool]
    show (1 / 3 : ℝ) + 2 / 3 = 1
    norm_num

/-- Test noise laws: `true` probability `1/4` at node 0 and `1/3` at node 1. -/
noncomputable def xorTestNoise : (k : Fin 2) → StdSimplex ℝ Bool := fun k =>
  if k.val = 0 then xorTestMu14 else xorTestMu13

/-- Noise weights of the four noise values. -/
theorem xorTest_w00 : noiseWeight xorTestNoise ![false, false] = (3/4 : ℝ) * (2/3) := by
  have h0 : (xorTestNoise 0).weights (![false, false] 0) = (3/4 : ℝ) := rfl
  have h1 : (xorTestNoise 1).weights (![false, false] 1) = (2/3 : ℝ) := rfl
  unfold noiseWeight
  rw [Fin.prod_univ_two, h0, h1]

theorem xorTest_w01 : noiseWeight xorTestNoise ![false, true] = (3/4 : ℝ) * (1/3) := by
  have h0 : (xorTestNoise 0).weights (![false, true] 0) = (3/4 : ℝ) := rfl
  have h1 : (xorTestNoise 1).weights (![false, true] 1) = (1/3 : ℝ) := rfl
  unfold noiseWeight
  rw [Fin.prod_univ_two, h0, h1]

theorem xorTest_w11 : noiseWeight xorTestNoise ![true, true] = (1/4 : ℝ) * (1/3) := by
  have h0 : (xorTestNoise 0).weights (![true, true] 0) = (1/4 : ℝ) := rfl
  have h1 : (xorTestNoise 1).weights (![true, true] 1) = (1/3 : ℝ) := rfl
  unfold noiseWeight
  rw [Fin.prod_univ_two, h0, h1]

/-- Evidence `E x := x 1 = false` on the four factual solutions. -/
theorem xorTest_e00 : xorTestModel.solve ![false, false] 1 = false := by decide
theorem xorTest_e01 : ¬ (xorTestModel.solve ![false, true] 1 = false) := by decide
theorem xorTest_e10 : ¬ (xorTestModel.solve ![true, false] 1 = false) := by decide
theorem xorTest_e11 : xorTestModel.solve ![true, true] 1 = false := by decide

/-- Event `F x := x 1 = true` on the four counterfactual solutions under `do(X_0 = false)`. -/
theorem xorTest_f00 : ¬ ((xorTestModel.counterfactual 0 false ![false, false]) 1 = true) := by
  decide
theorem xorTest_f01 : (xorTestModel.counterfactual 0 false ![false, true]) 1 = true := by
  decide
theorem xorTest_f10 : ¬ ((xorTestModel.counterfactual 0 false ![true, false]) 1 = true) := by
  decide
theorem xorTest_f11 : (xorTestModel.counterfactual 0 false ![true, true]) 1 = true := by
  decide

/-- A sum over the four noise values, as an explicit sum. -/
theorem sum_xorTest_four (g : ((k : Fin 2) → Bool) → ℝ) :
    ∑ u, g u
      = (g ![true, true] + g ![true, false]) + (g ![false, true] + g ![false, false]) := by
  have h := (piFinTwoEquiv (fun _ => Bool)).symm.sum_comp g
  rw [← h, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool,
    show ∀ a b : Bool, (piFinTwoEquiv (fun _ => Bool)).symm (a, b) = ![a, b] from
      fun a b => rfl]

/-- (a) The evidence has probability `7/12`. -/
theorem xorTest_evidenceProb :
    xorTestModel.evidenceProb xorTestNoise (fun x : Fin 2 → Bool => x 1 = false) = 7 / 12 := by
  simp only [evidenceProb, Finset.sum_filter, sum_xorTest_four, xorTest_e00, xorTest_e01,
    xorTest_e10, xorTest_e11, xorTest_w00, xorTest_w11]
  norm_num

example :
    xorTestModel.evidenceProb xorTestNoise (fun x : Fin 2 → Bool => x 1 = false) = 7 / 12 :=
  xorTest_evidenceProb

/-- (b) The counterfactual probability given the evidence is `1/7`. -/
theorem xorTest_counterfactualProb :
    xorTestModel.counterfactualProb xorTestNoise (fun x : Fin 2 → Bool => x 1 = false) 0 false
      (fun x : Fin 2 → Bool => x 1 = true) = 1 / 7 := by
  simp only [counterfactualProb, Finset.sum_filter, sum_xorTest_four, xorTest_e00, xorTest_e01,
    xorTest_e10, xorTest_e11, xorTest_f00, xorTest_f01, xorTest_f10, xorTest_f11, xorTest_w11,
    xorTest_evidenceProb]
  norm_num

example :
    xorTestModel.counterfactualProb xorTestNoise (fun x : Fin 2 → Bool => x 1 = false) 0 false
      (fun x : Fin 2 → Bool => x 1 = true) = 1 / 7 :=
  xorTest_counterfactualProb

/-- Trivial evidence has probability `1`. -/
theorem xorTest_evidenceTrue : xorTestModel.evidenceProb xorTestNoise (fun _ => True) = 1 := by
  simp only [evidenceProb, Finset.filter_true]
  exact sum_noiseWeight_eq_one _

/-- (c) Without evidence the counterfactual probability is `1/3`, differing from (b). -/
theorem xorTest_counterfactualTrue :
    xorTestModel.counterfactualProb xorTestNoise (fun _ => True) 0 false
      (fun x : Fin 2 → Bool => x 1 = true) = 1 / 3 := by
  simp only [counterfactualProb, Finset.sum_filter, sum_xorTest_four, true_and, xorTest_f00,
    xorTest_f01, xorTest_f10, xorTest_f11, xorTest_w01, xorTest_w11, xorTest_evidenceTrue]
  norm_num

example :
    xorTestModel.counterfactualProb xorTestNoise (fun _ => True) 0 false
      (fun x : Fin 2 → Bool => x 1 = true) = 1 / 3 :=
  xorTest_counterfactualTrue

end Counterfactuals

end Cslib.MachineLearning.StructuralCausalModelsTests
