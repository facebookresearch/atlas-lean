/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.StructuralCausalModels
public meta import CSLibExt.MachineLearning.GraphicalModels.StructuralCausalModels
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
* after surgery on the set `{0}` with value `true` the law of `(true, false)` is `1/3`;
* node `1` starts with the nonempty parent set `{0}`; after `do(X_1 = false)`, and after surgery
  on the set `{0, 1}`, its parent set is empty and its solution is `false` at every noise value;
* after `do(X_1 = false)` the law of `(true, false)` is `1/4`.

Counterfactuals in the same xor model, with evidence `X_1 = false` and `do(X_0 = false)`:

* the evidence has probability `7/12`;
* `P(X_1 = true had X_0 been false | X_1 = false) = 1/7`, while the interventional probability
  `P(X_1 = true | do(X_0 = false))` is `1/3`: sharing the noise between the factual and the
  counterfactual world matters.

With noise on `ℕ`, which has no `Fintype` instance, trivial evidence has probability `1`, the
posterior sums to `1`, and `counterfactualProb_true` applies.

Effectiveness, consistency and composition in the xor model (without noise laws): at
`u = (true, true)` the solution is `(true, false)`, setting `X_0 = true` changes nothing, and
additionally setting `X_1 = false` changes nothing; at `u = (false, true)` setting `X_0 = true`
gives `(true, false)` against the factual `(false, true)`.
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

/-- `inducedLaw_eq_joint` applies to noise types that are not finite: a finitely
supported law on `ℕ` needs no `Fintype ℕ` instance. -/
example (M : FiniteSCM Bool 1 (fun _ => ℕ)) (μ : (k : Fin 1) → StdSimplex ℝ ℕ)
    (x : Fin 1 → Bool) : M.inducedLaw μ x = (M.inducedBayesNet μ).joint x :=
  M.inducedLaw_eq_joint μ x

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

private def chainPa {n : ℕ} (k : Fin n) : Finset (Fin k) :=
  if h : 0 < k.val then {⟨k.val - 1, Nat.sub_lt h (by decide)⟩} else ∅

private def chainModel (n : ℕ) : FiniteSCM ℕ n (fun _ => Unit) where
  pa := chainPa
  f k z _ := if h : 0 < k.val then
    z ⟨⟨k.val - 1, Nat.sub_lt h (by decide)⟩, by simp [chainPa, h]⟩ + 1
    else 1

-- Exercise the compiled solver at increasing sizes, not just its equations.
#eval show IO Unit from do
  for n in [7, 15, 31, 63] do
    let result := (chainModel (n + 1)).solve (fun _ => ()) (Fin.last n)
    unless result == n + 1 do
      throw (IO.userError s!"chain of length {n + 1}: got {result}")

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

/-- The node-0 push-forward factor at `true` is `1/4`: node 0 copies its noise. -/
theorem map0_weights (g : paXor 0 → Bool) : ((μ 0).map (fXor 0 g)).weights true = 1 / 4 := by
  have hid : fXor 0 g = id := funext fun v => fXor_zero g v
  have hμ0 : μ 0 = μ0 := by simp [μ]
  rw [hid, StdSimplex.map_id, hμ0, μ0_true]

/-- Before surgery, node `1` has the nonempty parent set `{0}`. -/
example : (M.pa 1).Nonempty := by
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  simp only [M, paXor, dite_eq_right h10]
  exact Finset.singleton_nonempty _

/-- Surgery on node `1` deletes its parents. -/
example : (M.doNode 1 false).pa 1 = ∅ := by
  simp [FiniteSCM.doNode]

/-- Surgery on a set containing node `1` deletes its parents. -/
example : (M.doSet {0, 1} ![true, false]).pa 1 = ∅ := by
  simp [FiniteSCM.doSet]

/-- After surgery on node `1`, its solution is the intervention value at every noise value. -/
example (u : (k : Fin 2) → Bool) : (M.doNode 1 false).solve u 1 = false := by
  have h := (M.doNode 1 false).solve_isSolution u 1
  rw [M.doNode_f_of_eq] at h
  exact h

/-- After surgery on a set containing node `1`, its solution is the intervention value. -/
example (u : (k : Fin 2) → Bool) : (M.doSet {0, 1} ![true, false]).solve u 1 = false := by
  have h1W : (1 : Fin 2) ∈ ({0, 1} : Finset (Fin 2)) := by simp
  have h := (M.doSet {0, 1} ![true, false]).solve_isSolution u 1
  rw [M.doSet_f_of_mem _ _ h1W] at h
  simpa using h

/-- After `do(X_1 = false)`, the law of `(true, false)` is the probability `1/4` of
`X_0 = true`. -/
example : (M.doNode 1 false).inducedLaw μ ![true, false] = 1 / 4 := by
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have hx0 : (![true, false] : Fin 2 → Bool) 0 = true := by simp
  have hfac1 : ∀ z : ((M.inducedBayesNet μ).intervene 1 false).pa 1 → Bool,
      (((M.inducedBayesNet μ).intervene 1 false).cpt 1 z).weights
        ((![true, false] : Fin 2 → Bool) 1) = 1 := by
    intro z
    have hcpt : ((M.inducedBayesNet μ).intervene 1 false).cpt 1 z
        = StdSimplex.single false := by
      simp [BayesNet.intervene]
    rw [hcpt]
    have hx1 : (![true, false] : Fin 2 → Bool) 1 = false := by simp
    rw [hx1]
    simp [StdSimplex.weights_single]
  rw [FiniteSCM.inducedLaw_doNode, BayesNet.joint_eq_prod, Fin.prod_univ_two, hfac1, mul_one,
    hx0]
  simp only [BayesNet.intervene, dite_eq_right h01, FiniteSCM.inducedBayesNet, M]
  exact map0_weights _

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

/-- Both test noise laws give every value positive weight, so the product of their supports,
over which the counterfactual sums run, is every noise value. -/
theorem xorTest_support :
    Fintype.piFinset (fun k => (xorTestNoise k).weights.support) = Finset.univ := by
  have h : ∀ k, (xorTestNoise k).weights.support = Finset.univ := by
    intro k
    refine Finset.eq_univ_of_forall fun b => Finsupp.mem_support_iff.mpr ?_
    fin_cases k <;> cases b
    · show (3 / 4 : ℝ) ≠ 0
      norm_num
    · show (1 / 4 : ℝ) ≠ 0
      norm_num
    · show (2 / 3 : ℝ) ≠ 0
      norm_num
    · show (1 / 3 : ℝ) ≠ 0
      norm_num
  simp only [h, Fintype.piFinset_univ]

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
  simp only [evidenceProb, xorTest_support, Finset.sum_filter, sum_xorTest_four, xorTest_e00,
    xorTest_e01, xorTest_e10, xorTest_e11, xorTest_w00, xorTest_w11]
  norm_num

example :
    xorTestModel.evidenceProb xorTestNoise (fun x : Fin 2 → Bool => x 1 = false) = 7 / 12 :=
  xorTest_evidenceProb

/-- (b) The counterfactual probability given the evidence is `1/7`. -/
theorem xorTest_counterfactualProb :
    xorTestModel.counterfactualProb xorTestNoise (fun x : Fin 2 → Bool => x 1 = false) 0 false
      (fun x : Fin 2 → Bool => x 1 = true) = 1 / 7 := by
  simp only [counterfactualProb, xorTest_support, Finset.sum_filter, sum_xorTest_four,
    xorTest_e00, xorTest_e01, xorTest_e10, xorTest_e11, xorTest_f00, xorTest_f01, xorTest_f10,
    xorTest_f11, xorTest_w11, xorTest_evidenceProb]
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
  simp only [counterfactualProb, xorTest_support, Finset.sum_filter, sum_xorTest_four, true_and,
    xorTest_f00, xorTest_f01, xorTest_f10, xorTest_f11, xorTest_w01, xorTest_w11,
    xorTest_evidenceTrue]
  norm_num

example :
    xorTestModel.counterfactualProb xorTestNoise (fun _ => True) 0 false
      (fun x : Fin 2 → Bool => x 1 = true) = 1 / 3 :=
  xorTest_counterfactualTrue

/-! The counterfactual API needs no finiteness of the noise types: below, the noise of a
one-node model lives on `ℕ`, which has no `Fintype` instance. -/

/-- Trivial evidence has probability `1` for any noise laws on `ℕ`. -/
example (M : FiniteSCM Bool 1 (fun _ => ℕ)) (μ : (k : Fin 1) → StdSimplex ℝ ℕ) :
    M.evidenceProb μ (fun _ => True) = 1 := by
  simp only [evidenceProb, Finset.filter_true]
  exact sum_noiseWeight_eq_one μ

/-- The posterior given evidence of positive probability sums to `1` with noise on `ℕ`. -/
example (M : FiniteSCM Bool 1 (fun _ => ℕ)) (μ : (k : Fin 1) → StdSimplex ℝ ℕ)
    (E : (Fin 1 → Bool) → Prop) [DecidablePred E] (hE : M.evidenceProb μ E ≠ 0) :
    ∑ u ∈ Fintype.piFinset (fun j => (μ j).weights.support), M.posteriorWeight μ E u = 1 :=
  (M.sum_posteriorWeight μ E hE).2

/-- Without evidence the counterfactual probability is the interventional one, with noise on
`ℕ`. -/
example (M : FiniteSCM Bool 1 (fun _ => ℕ)) (μ : (k : Fin 1) → StdSimplex ℝ ℕ)
    (F : (Fin 1 → Bool) → Prop) [DecidablePred F] :
    M.counterfactualProb μ (fun _ => True) 0 true F =
      ∑ x with F x, (@BayesNet.joint Bool _ ⟨true⟩
        ((M.inducedBayesNet μ).intervene 0 true) x) :=
  M.counterfactualProb_true μ 0 true F

end Counterfactuals

namespace Consistency

def xorPa : (k : Fin 2) → Finset (Fin k) := fun k =>
  if h : k.val = 0 then ∅ else {⟨0, by have hk := k.2; omega⟩}

def xorF : (k : Fin 2) → (xorPa k → Bool) → Bool → Bool := fun k =>
  if h : k.val = 0 then fun _ u => u
  else fun z u => xor (z ⟨⟨0, by have hk := k.2; omega⟩, by simp [xorPa, h]⟩) u

def xorM : FiniteSCM Bool 2 (fun _ => Bool) := ⟨xorPa, xorF⟩

def xorU : (k : Fin 2) → Bool := ![true, true]

def xorU' : (k : Fin 2) → Bool := ![false, true]

example : xorM.solve xorU = ![true, false] := by decide

example : xorM.counterfactual 0 true xorU = xorM.solve xorU := by
  have ha : xorM.solve xorU = ![true, false] := by decide
  have h0 : xorM.solve xorU 0 = true := by rw [ha]; decide
  exact counterfactual_eq_solve _ h0

example : ((xorM.doNode 0 true).doNode 1 false).solve xorU = ![true, false] := by
  have ha : xorM.solve xorU = ![true, false] := by decide
  have h0 : xorM.solve xorU 0 = true := by rw [ha]; decide
  have hb : xorM.counterfactual 0 true xorU = xorM.solve xorU :=
    counterfactual_eq_solve _ h0
  have h1 : xorM.counterfactual 0 true xorU 1 = false := by rw [hb, ha]; decide
  have hc := solve_doNode_doNode_of_counterfactual (M := xorM) h1
  rw [hc, hb, ha]

example : xorM.counterfactual 0 true xorU' = ![true, false] ∧
    xorM.solve xorU' = ![false, true] := by
  constructor <;> decide

example : xorM.counterfactual 0 false xorU 0 = false :=
  counterfactual_self xorM 0 false xorU

end Consistency


namespace PotentialOutcomes

open Convexity MeasureTheory MathlibExt.Probability.Causality

/-! ### Test: xor model (`α = Bool`, `n = 2`). -/

noncomputable def ca04t03_xorμ0 : StdSimplex ℝ Bool where
  weights := Finsupp.single true (1/4 : ℝ) + Finsupp.single false (3/4 : ℝ)
  nonneg := by
    intro x
    cases x <;> simp [Finsupp.add_apply, Finsupp.single_apply] <;> norm_num
  total := by
    (simp [Finsupp.sum_add_index, Finsupp.sum_single_index]; norm_num)

noncomputable def ca04t03_xorμ1 : StdSimplex ℝ Bool where
  weights := Finsupp.single true (1/3 : ℝ) + Finsupp.single false (2/3 : ℝ)
  nonneg := by
    intro x
    cases x <;> simp [Finsupp.add_apply, Finsupp.single_apply] <;> norm_num
  total := by
    (simp [Finsupp.sum_add_index, Finsupp.sum_single_index]; norm_num)

noncomputable def ca04t03_xorμ : (k : Fin 2) → StdSimplex ℝ Bool
  | ⟨0, _⟩ => ca04t03_xorμ0
  | ⟨1, _⟩ => ca04t03_xorμ1
  | ⟨n + 2, h⟩ => absurd h (by omega)

noncomputable def ca04t03_xorM : FiniteSCM Bool 2 (fun _ => Bool) where
  pa := fun _ => Finset.univ
  f := fun k =>
    match k with
    | ⟨0, _⟩ => fun _ u => u
    | ⟨1, _⟩ => fun z u =>
        if z ⟨(⟨0, by decide⟩ : Fin 1), Finset.mem_univ _⟩ then !u else u
    | ⟨n + 2, h⟩ => absurd h (by omega)

noncomputable def ca04t03_xorG : Bool → ℝ := fun b => if b then 1 else 0

/-! The noise law is registered as a probability measure, so probability APIs such as
`integral_ipw_ate` find the instance. -/

example {n : ℕ} {U : Fin n → Type*} [∀ k, Fintype (U k)] [∀ k, MeasurableSpace (U k)]
    (μ : (k : Fin n) → StdSimplex ℝ (U k)) : IsProbabilityMeasure (noiseMeasure μ) := by
  infer_instance

example : IsProbabilityMeasure (noiseMeasure ca04t03_xorμ) := by
  infer_instance

theorem ca04t03_xor_solve_zero (u : (k : Fin 2) → Bool) :
    ca04t03_xorM.solve u ⟨0, by omega⟩ = u ⟨0, by omega⟩ := by
  have h := ca04t03_xorM.solve_isSolution u ⟨0, by omega⟩
  have h0 : ∀ (z : ca04t03_xorM.pa ⟨0, by omega⟩ → Bool) (v : Bool),
      ca04t03_xorM.f ⟨0, by omega⟩ z v = v := fun _ _ => rfl
  rw [h0] at h
  exact h

theorem ca04t03_xor_weights_true0 : (ca04t03_xorμ ⟨0, by omega⟩).weights true = (1/4 : ℝ) := by
  show (Finsupp.single true (1/4 : ℝ) + Finsupp.single false (3/4 : ℝ)) true = _
  simp [Finsupp.add_apply, Finsupp.single_apply]

theorem ca04t03_xor_weights_false0 : (ca04t03_xorμ ⟨0, by omega⟩).weights false = (3/4 : ℝ) := by
  show (Finsupp.single true (1/4 : ℝ) + Finsupp.single false (3/4 : ℝ)) false = _
  simp [Finsupp.add_apply, Finsupp.single_apply]

example : (noiseMeasure ca04t03_xorμ).real (ca04t03_xorM.treated ⟨0, by omega⟩ true) = 1/4 := by
  classical
  have hT : ca04t03_xorM.treated ⟨0, by omega⟩ true
      = {u | u ⟨0, by omega⟩ = true} := by
    ext u
    show (ca04t03_xorM.solve u ⟨0, by omega⟩ = true) ↔ (u ⟨0, by omega⟩ = true)
    rw [ca04t03_xor_solve_zero]
  rw [hT, real_coord_eq ca04t03_xorμ ⟨0, by omega⟩ (fun v => v = true), Finset.sum_filter]
  simp only [Fintype.sum_bool]
  rw [ite_true, ite_eq_right (by decide : ¬(false = true : Prop)), add_zero]
  rw [ca04t03_xor_weights_true0]

example : ca04t03_xorM.potentialOutcome ⟨0, by omega⟩ false ⟨1, by omega⟩ ca04t03_xorG
    ![true, true] = 1 := by
  rfl

example : ca04t03_xorM.potentialOutcome ⟨0, by omega⟩ true ⟨1, by omega⟩ ca04t03_xorG
    ![true, true] = 0 := by
  rfl

example : StronglyIgnorable (noiseMeasure ca04t03_xorμ) (ca04t03_xorM.treated ⟨0, by omega⟩ true)
    (fun u => (ca04t03_xorM.potentialOutcome ⟨0, by omega⟩ false ⟨1, by omega⟩ ca04t03_xorG u,
      ca04t03_xorM.potentialOutcome ⟨0, by omega⟩ true ⟨1, by omega⟩ ca04t03_xorG u))
    (fun _ => ()) := by
  classical
  apply stronglyIgnorable_of_pa_eq_empty
  · show (Finset.univ : Finset (Fin 0)) = ∅
    simp
  · intro w
    have hf : ∀ v, ca04t03_xorM.f ⟨0, by omega⟩ w v = v := fun v => rfl
    have hmap : ((ca04t03_xorμ ⟨0, by omega⟩).map (ca04t03_xorM.f ⟨0, by omega⟩ w)).weights true
        = (1/4 : ℝ) := by
      rw [map_weights_eq]
      simp only [hf]
      simp only [Fintype.sum_bool]
      rw [ca04t03_xor_weights_true0]
      norm_num
    rw [hmap]
    norm_num

end PotentialOutcomes


namespace Backdoor

open Convexity MeasureTheory MathlibExt.Probability.Causality

/-- A descendant never precedes its ancestor in the node order: every edge goes forward. -/
private theorem ca05t04_desc_val_le {α : Type*} {n : ℕ} (b : BayesNet α n) {i j : Fin n}
    (h : b.IsDescendant i j) : i.val ≤ j.val := by
  unfold BayesNet.IsDescendant at h
  induction h with
  | refl => exact le_rfl
  | tail _ h2 ih => exact ih.trans h2.1.le

/-! ### CA05.T04 tests: three-node confounded model on `Bool`. -/

/-- Test model `Z → T → Y`, `Z → Y` on `Bool`: node `0` is the confounder, node `1` the
treatment, node `2` the outcome. Parents: `pa 0 = ∅`, `pa 1 = {0}`, `pa 2 = {0, 1}`
(`univ` of `Fin 1` is `{0}`). -/
def ca05t04_testSCM : FiniteSCM Bool 3 (fun _ => Bool) where
  pa := fun k => if k.val = 0 then ∅ else Finset.univ
  f := fun _ _ u => u

/-- Test noise laws: point mass on `true`. -/
noncomputable def ca05t04_testMu : (k : Fin 3) → StdSimplex ℝ Bool :=
  fun _ => StdSimplex.single true

theorem ca05t04_test_hdesc : ∀ z ∈ ({0} : Finset (Fin 3)),
    ¬ (ca05t04_testSCM.inducedBayesNet ca05t04_testMu).IsDescendant 1 z := by
  intro z hz
  simp only [Finset.mem_singleton] at hz
  subst hz
  intro h
  have hle := ca05t04_desc_val_le (ca05t04_testSCM.inducedBayesNet ca05t04_testMu) h
  exact absurd hle (by decide)

theorem ca05t04_test_hblock : ∀ p, (ca05t04_testSCM.inducedBayesNet ca05t04_testMu).IsPath 1 2 p →
    (∃ h : 1 < p.length, (ca05t04_testSCM.inducedBayesNet ca05t04_testMu).Edge p[1] 1) →
      (ca05t04_testSCM.inducedBayesNet ca05t04_testMu).PathBlocked
        (↑({0} : Finset (Fin 3)) : Set (Fin 3)) p := by
  intro p hp hex
  obtain ⟨hnd, hchain, hhead, hlast⟩ := hp
  obtain ⟨hlen1, hedge⟩ := hex
  have hlen0 : 0 < p.length := by omega
  have h0 : p[0] = 1 := by
    rw [List.head?_eq_getElem?] at hhead
    rw [List.getElem?_eq_getElem hlen0] at hhead
    simpa using hhead
  have h1 : p[1] = 0 := by
    obtain ⟨hlt, -⟩ := hedge
    have hv1 : (1 : Fin 3).val = 1 := rfl
    have hv0 : p[1].val = 0 := by omega
    exact Fin.ext hv0
  have h1' : p[0 + 1] = (0 : Fin 3) := h1
  by_cases hlen2 : p.length = 2
  · have hlen1' : p.length - 1 = 1 := by omega
    rw [List.getLast?_eq_getElem?, hlen1', List.getElem?_eq_getElem hlen1] at hlast
    have h12 : p[1] = 2 := by simpa using hlast
    rw [h1] at h12
    exact absurd h12 (by decide)
  · have hib : 0 + 2 < p.length := by omega
    refine ⟨0, hib, Or.inr ⟨?_, ?_⟩⟩
    · intro hcon
      obtain ⟨e10, -⟩ := hcon
      obtain ⟨hlt10, -⟩ := e10
      rw [h0, h1'] at hlt10
      exact absurd hlt10 (by decide)
    · rw [h1']
      simp

/-- Test instance of `condIndepDiscrete_of_backdoor` on the confounded model. -/
example : CondIndepDiscrete (noiseMeasure ca05t04_testMu) (ca05t04_testSCM.treated 1 true)
    (ca05t04_testSCM.potentialOutcome 1 true 2 (fun b => if b then (1 : ℝ) else 0))
    (fun u (i : ({0} : Finset (Fin 3))) => ca05t04_testSCM.solve u i) := by
  letI : MeasurableSpace Bool := ⊤
  haveI : MeasurableSingletonClass Bool := ⟨fun _ => trivial⟩
  exact condIndepDiscrete_of_backdoor ca05t04_testSCM ca05t04_testMu 1 2 true true
    (fun b => if b then (1 : ℝ) else 0) {0} ca05t04_test_hdesc ca05t04_test_hblock


/-- Nondegenerate confounded model `Z → T → Y`, `Z → Y` on `Bool`: node `0` is the
confounder, node `1` the treatment, node `2` the outcome. Parents: `pa 0 = ∅`, `pa 1 = {0}`,
`pa 2 = {0, 1}`. All three noise laws are fair coins (strictly positive on `true` and `false`),
`T = Z ∨ U_T` genuinely depends on the confounder, and `Y = (Z ∧ T) ∨ U_Y` genuinely depends
on both `Z` and `T`. The interventional law `P(Y_{T←true} = true)` is `3/4` while the naive
observational conditional `P(Y = true | T = true)` is `5/6`, so adjustment matters. -/
def ca05t04_nd_pa : (k : Fin 3) → Finset (Fin k) :=
  fun k => if k.val = 0 then ∅ else Finset.univ

def ca05t04_nd_f : (k : Fin 3) → (ca05t04_nd_pa k → Bool) → Bool → Bool := fun k =>
  if h0 : k.val = 0 then fun _ u => u
  else if _h1 : k.val = 1 then fun z u =>
    (z ⟨⟨0, by have hk := k.2; omega⟩, by simp [ca05t04_nd_pa, h0]⟩) || u
  else fun z u =>
    ((z ⟨⟨0, by have hk := k.2; omega⟩, by simp [ca05t04_nd_pa, h0]⟩) &&
      (z ⟨⟨1, by have hk := k.2; omega⟩, by simp [ca05t04_nd_pa, h0]⟩)) || u

def ca05t04_nd_SCM : FiniteSCM Bool 3 (fun _ => Bool) := ⟨ca05t04_nd_pa, ca05t04_nd_f⟩

/-- A fair coin on `Bool`: strictly positive on both values. -/
noncomputable def ca05t04_nd_coin : StdSimplex ℝ Bool where
  weights := Finsupp.single true (1/2 : ℝ) + Finsupp.single false (1/2 : ℝ)
  nonneg := by
    intro x
    cases x <;> simp [Finsupp.add_apply, Finsupp.single_apply] <;> norm_num
  total := by
    first
      | (simp [Finsupp.sum_add_index, Finsupp.sum_single_index]; norm_num)
      | (simp [Finsupp.sum_add_index', Finsupp.sum_single_index]; norm_num)
      | (rw [Finsupp.sum_fintype (fun _ => rfl)]
         simp [Fintype.sum_bool, Finsupp.add_apply, Finsupp.single_apply]
         norm_num)

/-- Test noise laws: a fair coin at every node. -/
noncomputable def ca05t04_nd_μ : (k : Fin 3) → StdSimplex ℝ Bool :=
  fun _ => ca05t04_nd_coin

theorem ca05t04_nd_w_true (k : Fin 3) : (ca05t04_nd_μ k).weights true = (1/2 : ℝ) := by
  show (Finsupp.single true (1/2 : ℝ) + Finsupp.single false (1/2 : ℝ)) true = _
  simp [Finsupp.add_apply, Finsupp.single_apply]

theorem ca05t04_nd_w_false (k : Fin 3) : (ca05t04_nd_μ k).weights false = (1/2 : ℝ) := by
  show (Finsupp.single true (1/2 : ℝ) + Finsupp.single false (1/2 : ℝ)) false = _
  simp [Finsupp.add_apply, Finsupp.single_apply]

/-- Both noise values have strictly positive weight at every node. -/
theorem ca05t04_nd_pos_true (k : Fin 3) : 0 < (ca05t04_nd_μ k).weights true := by
  rw [ca05t04_nd_w_true]; norm_num

theorem ca05t04_nd_pos_false (k : Fin 3) : 0 < (ca05t04_nd_μ k).weights false := by
  rw [ca05t04_nd_w_false]; norm_num

/-- Every noise value lies in the product of the supports of the fair-coin noise laws. -/
private theorem ca05t04_nd_mem_supp (u : (k : Fin 3) → Bool) :
    u ∈ Fintype.piFinset (fun j => (ca05t04_nd_μ j).weights.support) := by
  rw [Fintype.mem_piFinset]
  intro k
  rw [Finsupp.mem_support_iff]
  cases u k
  · exact (ca05t04_nd_pos_false k).ne'
  · exact (ca05t04_nd_pos_true k).ne'

/-- `T = Z ∨ U_T` genuinely depends on the confounder `Z`: flipping the parent value at fixed
noise flips the treatment. -/
example : ca05t04_nd_SCM.f 1 (fun _ => true) false
    ≠ ca05t04_nd_SCM.f 1 (fun _ => false) false := by
  decide

/-- `Y = (Z ∧ T) ∨ U_Y` genuinely depends on `Z`: varying the `Z` parent at fixed `T` parent
and fixed noise changes the outcome. -/
example : ca05t04_nd_SCM.f 2 (fun _ => true) false
    ≠ ca05t04_nd_SCM.f 2 (fun j => decide (j.val.val = 1)) false := by
  decide

/-- `Y = (Z ∧ T) ∨ U_Y` genuinely depends on `T`: varying the `T` parent at fixed `Z` parent
and fixed noise changes the outcome. -/
example : ca05t04_nd_SCM.f 2 (fun _ => true) false
    ≠ ca05t04_nd_SCM.f 2 (fun j => decide (j.val.val = 0)) false := by
  decide

/-- Every noise value has weight `(1/2)^3 = 1/8`. -/
theorem ca05t04_nd_weight_all (u : (k : Fin 3) → Bool) :
    noiseWeight ca05t04_nd_μ u = 1/8 := by
  unfold noiseWeight
  rw [Fin.prod_univ_three]
  cases h0 : u 0 <;> cases h1 : u 1 <;> cases h2 : u 2 <;>
    simp only [ca05t04_nd_w_true, ca05t04_nd_w_false] <;> norm_num

/-- Enumeration of the eight noise values. -/
def ca05t04_nd_equiv : ((k : Fin 3) → Bool) ≃ Bool × Bool × Bool where
  toFun u := (u 0, u 1, u 2)
  invFun p := ![p.1, p.2.1, p.2.2]
  left_inv u := by funext k; fin_cases k <;> simp
  right_inv p := by obtain ⟨a, b, c⟩ := p; simp

/-- A sum over the noise values, as an explicit sum. -/
theorem ca05t04_nd_sum8 (g : ((k : Fin 3) → Bool) → ℝ) :
    ∑ u, g u
      = ((g ![true, true, true] + g ![true, true, false])
        + (g ![true, false, true] + g ![true, false, false]))
        + ((g ![false, true, true] + g ![false, true, false])
        + (g ![false, false, true] + g ![false, false, false])) := by
  have h := ca05t04_nd_equiv.symm.sum_comp g
  rw [← h]
  simp only [show ∀ p : Bool × Bool × Bool, ca05t04_nd_equiv.symm p = ![p.1, p.2.1, p.2.2]
    from fun p => rfl]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]

/-- Treatment values `T = Z ∨ U_T` on the eight noise values. -/
theorem ca05t04_nd_t_ttt : ca05t04_nd_SCM.solve ![true, true, true] 1 = true := by decide
theorem ca05t04_nd_t_ttf : ca05t04_nd_SCM.solve ![true, true, false] 1 = true := by decide
theorem ca05t04_nd_t_tft : ca05t04_nd_SCM.solve ![true, false, true] 1 = true := by decide
theorem ca05t04_nd_t_tff : ca05t04_nd_SCM.solve ![true, false, false] 1 = true := by decide
theorem ca05t04_nd_t_ftt : ca05t04_nd_SCM.solve ![false, true, true] 1 = true := by decide
theorem ca05t04_nd_t_ftf : ca05t04_nd_SCM.solve ![false, true, false] 1 = true := by decide
theorem ca05t04_nd_t_fft : ¬ (ca05t04_nd_SCM.solve ![false, false, true] 1 = true) := by decide
theorem ca05t04_nd_t_fff : ¬ (ca05t04_nd_SCM.solve ![false, false, false] 1 = true) := by decide

/-- `Y ∧ T` on the eight noise values. -/
theorem ca05t04_nd_n_ttt : ca05t04_nd_SCM.solve ![true, true, true] 2 = true ∧
    ca05t04_nd_SCM.solve ![true, true, true] 1 = true := by
  decide
theorem ca05t04_nd_n_ttf : ca05t04_nd_SCM.solve ![true, true, false] 2 = true ∧
    ca05t04_nd_SCM.solve ![true, true, false] 1 = true := by
  decide
theorem ca05t04_nd_n_tft : ca05t04_nd_SCM.solve ![true, false, true] 2 = true ∧
    ca05t04_nd_SCM.solve ![true, false, true] 1 = true := by
  decide
theorem ca05t04_nd_n_tff : ca05t04_nd_SCM.solve ![true, false, false] 2 = true ∧
    ca05t04_nd_SCM.solve ![true, false, false] 1 = true := by
  decide
theorem ca05t04_nd_n_ftt : ca05t04_nd_SCM.solve ![false, true, true] 2 = true ∧
    ca05t04_nd_SCM.solve ![false, true, true] 1 = true := by
  decide
theorem ca05t04_nd_n_ftf : ¬ (ca05t04_nd_SCM.solve ![false, true, false] 2 = true ∧
    ca05t04_nd_SCM.solve ![false, true, false] 1 = true) := by
  decide
theorem ca05t04_nd_n_fft : ¬ (ca05t04_nd_SCM.solve ![false, false, true] 2 = true ∧
    ca05t04_nd_SCM.solve ![false, false, true] 1 = true) := by
  decide
theorem ca05t04_nd_n_fff : ¬ (ca05t04_nd_SCM.solve ![false, false, false] 2 = true ∧
    ca05t04_nd_SCM.solve ![false, false, false] 1 = true) := by
  decide

/-- Counterfactual outcome `Y_{T←true} = Z ∨ U_Y` on the eight noise values. -/
theorem ca05t04_nd_c_ttt :
    ca05t04_nd_SCM.counterfactual 1 true ![true, true, true] 2 = true := by
  decide
theorem ca05t04_nd_c_ttf :
    ca05t04_nd_SCM.counterfactual 1 true ![true, true, false] 2 = true := by
  decide
theorem ca05t04_nd_c_tft :
    ca05t04_nd_SCM.counterfactual 1 true ![true, false, true] 2 = true := by
  decide
theorem ca05t04_nd_c_tff :
    ca05t04_nd_SCM.counterfactual 1 true ![true, false, false] 2 = true := by
  decide
theorem ca05t04_nd_c_ftt :
    ca05t04_nd_SCM.counterfactual 1 true ![false, true, true] 2 = true := by
  decide
theorem ca05t04_nd_c_ftf :
    ¬ (ca05t04_nd_SCM.counterfactual 1 true ![false, true, false] 2 = true) := by
  decide
theorem ca05t04_nd_c_fft :
    ca05t04_nd_SCM.counterfactual 1 true ![false, false, true] 2 = true := by
  decide
theorem ca05t04_nd_c_fff :
    ¬ (ca05t04_nd_SCM.counterfactual 1 true ![false, false, false] 2 = true) := by
  decide

/-- `T ∧ (Z = true)` on the eight noise values. -/
theorem ca05t04_nd_zt_ttt : ca05t04_nd_SCM.solve ![true, true, true] 1 = true ∧
    ca05t04_nd_SCM.solve ![true, true, true] 0 = true := by
  decide
theorem ca05t04_nd_zt_ttf : ca05t04_nd_SCM.solve ![true, true, false] 1 = true ∧
    ca05t04_nd_SCM.solve ![true, true, false] 0 = true := by
  decide
theorem ca05t04_nd_zt_tft : ca05t04_nd_SCM.solve ![true, false, true] 1 = true ∧
    ca05t04_nd_SCM.solve ![true, false, true] 0 = true := by
  decide
theorem ca05t04_nd_zt_tff : ca05t04_nd_SCM.solve ![true, false, false] 1 = true ∧
    ca05t04_nd_SCM.solve ![true, false, false] 0 = true := by
  decide
theorem ca05t04_nd_zt_ftt : ¬ (ca05t04_nd_SCM.solve ![false, true, true] 1 = true ∧
    ca05t04_nd_SCM.solve ![false, true, true] 0 = true) := by
  decide
theorem ca05t04_nd_zt_ftf : ¬ (ca05t04_nd_SCM.solve ![false, true, false] 1 = true ∧
    ca05t04_nd_SCM.solve ![false, true, false] 0 = true) := by
  decide
theorem ca05t04_nd_zt_fft : ¬ (ca05t04_nd_SCM.solve ![false, false, true] 1 = true ∧
    ca05t04_nd_SCM.solve ![false, false, true] 0 = true) := by
  decide
theorem ca05t04_nd_zt_fff : ¬ (ca05t04_nd_SCM.solve ![false, false, false] 1 = true ∧
    ca05t04_nd_SCM.solve ![false, false, false] 0 = true) := by
  decide

/-- `T ∧ (Z = false)` on the eight noise values. -/
theorem ca05t04_nd_zf_ttt : ¬ (ca05t04_nd_SCM.solve ![true, true, true] 1 = true ∧
    ca05t04_nd_SCM.solve ![true, true, true] 0 = false) := by
  decide
theorem ca05t04_nd_zf_ttf : ¬ (ca05t04_nd_SCM.solve ![true, true, false] 1 = true ∧
    ca05t04_nd_SCM.solve ![true, true, false] 0 = false) := by
  decide
theorem ca05t04_nd_zf_tft : ¬ (ca05t04_nd_SCM.solve ![true, false, true] 1 = true ∧
    ca05t04_nd_SCM.solve ![true, false, true] 0 = false) := by
  decide
theorem ca05t04_nd_zf_tff : ¬ (ca05t04_nd_SCM.solve ![true, false, false] 1 = true ∧
    ca05t04_nd_SCM.solve ![true, false, false] 0 = false) := by
  decide
theorem ca05t04_nd_zf_ftt : ca05t04_nd_SCM.solve ![false, true, true] 1 = true ∧
    ca05t04_nd_SCM.solve ![false, true, true] 0 = false := by
  decide
theorem ca05t04_nd_zf_ftf : ca05t04_nd_SCM.solve ![false, true, false] 1 = true ∧
    ca05t04_nd_SCM.solve ![false, true, false] 0 = false := by
  decide
theorem ca05t04_nd_zf_fft : ¬ (ca05t04_nd_SCM.solve ![false, false, true] 1 = true ∧
    ca05t04_nd_SCM.solve ![false, false, true] 0 = false) := by
  decide
theorem ca05t04_nd_zf_fff : ¬ (ca05t04_nd_SCM.solve ![false, false, false] 1 = true ∧
    ca05t04_nd_SCM.solve ![false, false, false] 0 = false) := by
  decide

/-- The naive numerator `P(Y = true ∧ T = true)` is `5/8`. -/
theorem ca05t04_nd_naive_num : (noiseMeasure ca05t04_nd_μ).real
    ({u | ca05t04_nd_SCM.solve u 2 = true} ∩ ca05t04_nd_SCM.treated 1 true) = 5/8 := by
  classical
  rw [noiseMeasure_real_eq]
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, treated, Finset.sum_filter,
    ca05t04_nd_sum8, ca05t04_nd_weight_all, ca05t04_nd_n_ttt, ca05t04_nd_n_ttf,
    ca05t04_nd_n_tft, ca05t04_nd_n_tff, ca05t04_nd_n_ftt, ca05t04_nd_n_ftf,
    ca05t04_nd_n_fft, ca05t04_nd_n_fff]
  norm_num

/-- The naive denominator `P(T = true)` is `3/4`. -/
theorem ca05t04_nd_naive_den : (noiseMeasure ca05t04_nd_μ).real
    (ca05t04_nd_SCM.treated 1 true) = 3/4 := by
  classical
  rw [noiseMeasure_real_eq]
  simp only [Set.mem_ofPred_eq, treated, Finset.sum_filter, ca05t04_nd_sum8,
    ca05t04_nd_weight_all, ca05t04_nd_t_ttt, ca05t04_nd_t_ttf, ca05t04_nd_t_tft,
    ca05t04_nd_t_tff, ca05t04_nd_t_ftt, ca05t04_nd_t_ftf, ca05t04_nd_t_fft,
    ca05t04_nd_t_fff]
  have hfeq : @Finset.filter (Fin 3 → Bool) (fun u => ca05t04_nd_SCM.solve u 1 = true)
      (fun a => Classical.propDecidable (a ∈ ca05t04_nd_SCM.treated 1 true)) Finset.univ =
      Finset.univ.filter (fun u => ca05t04_nd_SCM.solve u 1 = true) :=
    @Finset.filter_congr (Fin 3 → Bool) _ _
      (fun a => Classical.propDecidable (a ∈ ca05t04_nd_SCM.treated 1 true)) _
      Finset.univ (fun u _ => Iff.rfl)
  rw [Finset.sum_const, nsmul_eq_mul, hfeq]
  have hcard : (Finset.univ.filter (fun u => ca05t04_nd_SCM.solve u 1 = true)).card = 6 := by decide
  rw [hcard]
  norm_num

/-- The potential-outcome law `P(Y_{T←true} = true)` is `3/4`. -/
theorem ca05t04_nd_cf : (noiseMeasure ca05t04_nd_μ).real
    {u | ca05t04_nd_SCM.counterfactual 1 true u 2 = true} = 3/4 := by
  classical
  rw [noiseMeasure_real_eq]
  simp only [Set.mem_ofPred_eq, Finset.sum_filter, ca05t04_nd_sum8, ca05t04_nd_weight_all,
    ca05t04_nd_c_ttt, ca05t04_nd_c_ttf, ca05t04_nd_c_tft, ca05t04_nd_c_tff,
    ca05t04_nd_c_ftt, ca05t04_nd_c_ftf, ca05t04_nd_c_fft, ca05t04_nd_c_fff]
  norm_num

/-- The naive observational conditional `P(Y = true | T = true)` is `5/6`. -/
theorem ca05t04_nd_naive : (noiseMeasure ca05t04_nd_μ).real
      ({u | ca05t04_nd_SCM.solve u 2 = true} ∩ ca05t04_nd_SCM.treated 1 true) /
      (noiseMeasure ca05t04_nd_μ).real (ca05t04_nd_SCM.treated 1 true) = 5/6 := by
  rw [ca05t04_nd_naive_num, ca05t04_nd_naive_den]
  norm_num

/-- Adjustment matters: the potential-outcome law differs from the naive conditional. -/
theorem ca05t04_nd_matters : (noiseMeasure ca05t04_nd_μ).real
      {u | ca05t04_nd_SCM.counterfactual 1 true u 2 = true} ≠
      (noiseMeasure ca05t04_nd_μ).real
        ({u | ca05t04_nd_SCM.solve u 2 = true} ∩ ca05t04_nd_SCM.treated 1 true) /
        (noiseMeasure ca05t04_nd_μ).real (ca05t04_nd_SCM.treated 1 true) := by
  rw [ca05t04_nd_cf, ca05t04_nd_naive]
  norm_num

theorem ca05t04_nd_hdesc : ∀ z ∈ ({0} : Finset (Fin 3)),
    ¬ (ca05t04_nd_SCM.inducedBayesNet ca05t04_nd_μ).IsDescendant 1 z := by
  intro z hz
  simp only [Finset.mem_singleton] at hz
  subst hz
  intro h
  have hle := ca05t04_desc_val_le (ca05t04_nd_SCM.inducedBayesNet ca05t04_nd_μ) h
  exact absurd hle (by decide)

theorem ca05t04_nd_hblock : ∀ p, (ca05t04_nd_SCM.inducedBayesNet ca05t04_nd_μ).IsPath 1 2 p →
    (∃ h : 1 < p.length, (ca05t04_nd_SCM.inducedBayesNet ca05t04_nd_μ).Edge p[1] 1) →
      (ca05t04_nd_SCM.inducedBayesNet ca05t04_nd_μ).PathBlocked
        (↑({0} : Finset (Fin 3)) : Set (Fin 3)) p := by
  intro p hp hex
  obtain ⟨hnd, hchain, hhead, hlast⟩ := hp
  obtain ⟨hlen1, hedge⟩ := hex
  have hlen0 : 0 < p.length := by omega
  have h0 : p[0] = 1 := by
    rw [List.head?_eq_getElem?] at hhead
    rw [List.getElem?_eq_getElem hlen0] at hhead
    simpa using hhead
  have h1 : p[1] = 0 := by
    obtain ⟨hlt, -⟩ := hedge
    have hv1 : (1 : Fin 3).val = 1 := rfl
    have hv0 : p[1].val = 0 := by omega
    exact Fin.ext hv0
  have h1' : p[0 + 1] = (0 : Fin 3) := h1
  by_cases hlen2 : p.length = 2
  · have hlen1' : p.length - 1 = 1 := by omega
    rw [List.getLast?_eq_getElem?, hlen1', List.getElem?_eq_getElem hlen1] at hlast
    have h12 : p[1] = 2 := by simpa using hlast
    rw [h1] at h12
    exact absurd h12 (by decide)
  · have hib : 0 + 2 < p.length := by omega
    refine ⟨0, hib, Or.inr ⟨?_, ?_⟩⟩
    · intro hcon
      obtain ⟨e10, -⟩ := hcon
      obtain ⟨hlt10, -⟩ := e10
      rw [h0, h1'] at hlt10
      exact absurd hlt10 (by decide)
    · rw [h1']
      simp

/-- Test instance of `condIndepDiscrete_of_backdoor` on the nondegenerate confounded model. -/
example : CondIndepDiscrete (noiseMeasure ca05t04_nd_μ) (ca05t04_nd_SCM.treated 1 true)
    (ca05t04_nd_SCM.potentialOutcome 1 true 2 (fun b => if b then (1 : ℝ) else 0))
    (fun u (i : ({0} : Finset (Fin 3))) => ca05t04_nd_SCM.solve u i) := by
  letI : MeasurableSpace Bool := ⊤
  haveI : MeasurableSingletonClass Bool := ⟨fun _ => trivial⟩
  exact condIndepDiscrete_of_backdoor ca05t04_nd_SCM ca05t04_nd_μ 1 2 true true
    (fun b => if b then (1 : ℝ) else 0) {0} ca05t04_nd_hdesc ca05t04_nd_hblock

/-- The confounder value as an element of `Z = {0}`. -/
def ca05t04_nd_z0 : ↥(({0} : Finset (Fin 3))) := ⟨0, by simp⟩

/-- Node `0` copies its noise. -/
theorem ca05t04_nd_solve_zero (u : (k : Fin 3) → Bool) :
    ca05t04_nd_SCM.solve u 0 = u 0 := by
  have h := ca05t04_nd_SCM.solve_isSolution u 0
  have h0 : ∀ (zz : ca05t04_nd_SCM.pa 0 → Bool) (v : Bool),
      ca05t04_nd_SCM.f 0 zz v = v := fun _ _ => rfl
  rw [h0] at h
  exact h

/-- Agreement on `Z = {0}` is agreement at node `0`. -/
theorem ca05t04_nd_pred_iff (x : Fin 3 → Bool) (z : ↥(({0} : Finset (Fin 3))) → Bool) :
    (((fun i : ↥(({0} : Finset (Fin 3))) => x ↑i) = z) ↔
      (x 0 = z ca05t04_nd_z0)) := by
  constructor
  · intro h
    exact congrFun h ca05t04_nd_z0
  · intro h
    funext ⟨i, hi⟩
    have hi0 : i = 0 := Finset.mem_singleton.1 hi
    subst hi0
    exact h

/-- Positivity for the back-door formula at `a = true`: every `Z` value jointly with
`T = true` has positive probability. -/
theorem ca05t04_nd_hpos : ∀ z : ↥(({0} : Finset (Fin 3))) → Bool,
    (∑ x with (fun i : ↥(({0} : Finset (Fin 3))) => x ↑i) = z,
      (ca05t04_nd_SCM.inducedBayesNet ca05t04_nd_μ).joint x) ≠ 0 →
    (∑ x with x 1 = true ∧ (fun i : ↥(({0} : Finset (Fin 3))) => x ↑i) = z,
      (ca05t04_nd_SCM.inducedBayesNet ca05t04_nd_μ).joint x) ≠ 0 := by
  classical
  intro z _
  have hnoise_nonneg : ∀ u : (k : Fin 3) → Bool, 0 ≤ noiseWeight ca05t04_nd_μ u := by
    intro u
    unfold noiseWeight
    exact Finset.prod_nonneg fun k _ => (ca05t04_nd_μ k).nonneg _
  have hj_nonneg : ∀ x ∈ Finset.univ.filter
      (fun x => x 1 = true ∧ (fun i : ↥(({0} : Finset (Fin 3))) => x ↑i) = z),
      0 ≤ (ca05t04_nd_SCM.inducedBayesNet ca05t04_nd_μ).joint x := by
    intro x _
    exact (ca05t04_nd_SCM.inducedBayesNet ca05t04_nd_μ).toChain.joint_nonneg 3 x
  cases hcz : z ca05t04_nd_z0
  · -- `z` is `false` on `Z`: witness `![false, true, true]`.
    have hx1 : (![false, true, true] : Fin 3 → Bool) 1 = true := by simp
    have hx0_false : (![false, true, true] : Fin 3 → Bool) 0 = false := by simp
    have hx0_eq : (![false, true, true] : Fin 3 → Bool) 0 = z ca05t04_nd_z0 := by
      rw [hx0_false, hcz]
    have hxz : (fun i : ↥(({0} : Finset (Fin 3))) => (![false, true, true] : Fin 3 → Bool) ↑i) = z :=
      (ca05t04_nd_pred_iff _ _).mpr hx0_eq
    have hmem : (![false, true, true] : Fin 3 → Bool) ∈ Finset.univ.filter
        (fun x => x 1 = true ∧ (fun i : ↥(({0} : Finset (Fin 3))) => x ↑i) = z) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx1, hxz⟩
    have hsolve : ca05t04_nd_SCM.solve ![false, true, true] = ![false, true, true] := by decide
    have hu_pos : 0 < noiseWeight ca05t04_nd_μ ![false, true, true] := by
      rw [ca05t04_nd_weight_all]; norm_num
    have h_ind_pos : 0 < ca05t04_nd_SCM.inducedLaw ca05t04_nd_μ ![false, true, true] := by
      unfold inducedLaw
      refine Finset.sum_pos' (fun u _ => ?_) ⟨![false, true, true], ca05t04_nd_mem_supp _, ?_⟩
      · split_ifs
        · exact hnoise_nonneg u
        · exact le_rfl
      · rw [ite_eq_left hsolve]
        exact hu_pos
    have hj_eq : (ca05t04_nd_SCM.inducedBayesNet ca05t04_nd_μ).joint ![false, true, true] =
        ca05t04_nd_SCM.inducedLaw ca05t04_nd_μ ![false, true, true] :=
      (ca05t04_nd_SCM.inducedLaw_eq_joint ca05t04_nd_μ _).symm
    have hjpos : 0 < (ca05t04_nd_SCM.inducedBayesNet ca05t04_nd_μ).joint ![false, true, true] := by
      rw [hj_eq]; exact h_ind_pos
    have h_sum_pos : 0 < ∑ x with x 1 = true ∧
        (fun i : ↥(({0} : Finset (Fin 3))) => x ↑i) = z,
        (ca05t04_nd_SCM.inducedBayesNet ca05t04_nd_μ).joint x :=
      Finset.sum_pos' hj_nonneg ⟨_, hmem, hjpos⟩
    exact ne_of_gt h_sum_pos
  · -- `z` is `true` on `Z`: witness `![true, true, true]`.
    have hx1 : (![true, true, true] : Fin 3 → Bool) 1 = true := by simp
    have hx0_true : (![true, true, true] : Fin 3 → Bool) 0 = true := by simp
    have hx0_eq : (![true, true, true] : Fin 3 → Bool) 0 = z ca05t04_nd_z0 := by
      rw [hx0_true, hcz]
    have hxz : (fun i : ↥(({0} : Finset (Fin 3))) => (![true, true, true] : Fin 3 → Bool) ↑i) = z :=
      (ca05t04_nd_pred_iff _ _).mpr hx0_eq
    have hmem : (![true, true, true] : Fin 3 → Bool) ∈ Finset.univ.filter
        (fun x => x 1 = true ∧ (fun i : ↥(({0} : Finset (Fin 3))) => x ↑i) = z) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx1, hxz⟩
    have hsolve : ca05t04_nd_SCM.solve ![true, true, true] = ![true, true, true] := by decide
    have hu_pos : 0 < noiseWeight ca05t04_nd_μ ![true, true, true] := by
      rw [ca05t04_nd_weight_all]; norm_num
    have h_ind_pos : 0 < ca05t04_nd_SCM.inducedLaw ca05t04_nd_μ ![true, true, true] := by
      unfold inducedLaw
      refine Finset.sum_pos' (fun u _ => ?_) ⟨![true, true, true], ca05t04_nd_mem_supp _, ?_⟩
      · split_ifs
        · exact hnoise_nonneg u
        · exact le_rfl
      · rw [ite_eq_left hsolve]
        exact hu_pos
    have hj_eq : (ca05t04_nd_SCM.inducedBayesNet ca05t04_nd_μ).joint ![true, true, true] =
        ca05t04_nd_SCM.inducedLaw ca05t04_nd_μ ![true, true, true] :=
      (ca05t04_nd_SCM.inducedLaw_eq_joint ca05t04_nd_μ _).symm
    have hjpos : 0 < (ca05t04_nd_SCM.inducedBayesNet ca05t04_nd_μ).joint ![true, true, true] := by
      rw [hj_eq]; exact h_ind_pos
    have h_sum_pos : 0 < ∑ x with x 1 = true ∧
        (fun i : ↥(({0} : Finset (Fin 3))) => x ↑i) = z,
        (ca05t04_nd_SCM.inducedBayesNet ca05t04_nd_μ).joint x :=
      Finset.sum_pos' hj_nonneg ⟨_, hmem, hjpos⟩
    exact ne_of_gt h_sum_pos

/-- The potential-outcome law equals the back-door adjustment formula on this model. -/
example : (noiseMeasure ca05t04_nd_μ).real
      {u | ca05t04_nd_SCM.counterfactual 1 true u 2 = true}
    = ∑ z : ↥(({0} : Finset (Fin 3))) → Bool,
      (∑ x with (fun i : ↥(({0} : Finset (Fin 3))) => x ↑i) = z,
        (ca05t04_nd_SCM.inducedBayesNet ca05t04_nd_μ).joint x) *
      ((∑ x with x 1 = true ∧ x 2 = true ∧
        (fun i : ↥(({0} : Finset (Fin 3))) => x ↑i) = z,
        (ca05t04_nd_SCM.inducedBayesNet ca05t04_nd_μ).joint x) /
      ∑ x with x 1 = true ∧ (fun i : ↥(({0} : Finset (Fin 3))) => x ↑i) = z,
        (ca05t04_nd_SCM.inducedBayesNet ca05t04_nd_μ).joint x) := by
  letI : MeasurableSpace Bool := ⊤
  haveI : MeasurableSingletonClass Bool := ⟨fun _ => trivial⟩
  exact measureReal_counterfactual_eq_backdoor ca05t04_nd_SCM ca05t04_nd_μ 1 2 {0} true
    true (by decide) (by decide) ca05t04_nd_hdesc ca05t04_nd_hblock ca05t04_nd_hpos

end Backdoor

end Cslib.MachineLearning.StructuralCausalModelsTests
