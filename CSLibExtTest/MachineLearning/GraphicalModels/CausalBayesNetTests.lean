/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.CausalBayesNet
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring

/-!
# Tests for causal Bayesian networks

* A confounded network `Z → X → Y`, `Z → Y` on `Bool`: the truncated factorization after
  `do(X = true)` at two assignments, and the adjustment formulas for the parents and for the
  predecessor set `{Z}` (whose positivity hypotheses hold since every table gives both values
  positive probability).
* d-separation: in the chain `0 → 1 → 2` the path `0, 1, 2` is blocked by `{1}`; in the
  collider `0 → 2 ← 1` conditioning on the collider opens the path `0, 2, 1`, so `{2}` does not
  d-separate `0` from `1`.
-/

@[expose] public section

namespace Cslib.MachineLearning.CausalBayesNetTests

open Cslib.MachineLearning GraphicalModels Convexity Finset

/-- The distribution on `Bool` with `P(true) = p`. -/
noncomputable def coin (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : StdSimplex ℝ Bool :=
  StdSimplex.duple (t := 1 - p) true false h0 (by linarith) (by ring)

theorem coin_true (p : ℝ) (h0 h1) : (coin p h0 h1).weights true = p := by
  simp [coin, StdSimplex.duple]

theorem coin_false (p : ℝ) (h0 h1) : (coin p h0 h1).weights false = 1 - p := by
  simp [coin, StdSimplex.duple]

/-- The confounded network: `Z` (node 0) is a fair coin; `X` (node 1) is `true` with
probability `4/5` if `Z` and `1/5` otherwise; `Y` (node 2) is `true` with probability
`9/10`, `1/2`, `1/2`, `1/10` for `(X, Z) = (true, true), (true, false), (false, true),
(false, false)`. -/
noncomputable def confNet : BayesNet Bool 3 where
  pa k := univ
  cpt k u := if h0 : (k : ℕ) = 0 then coin (1 / 2) (by norm_num) (by norm_num) else
    if h1 : (k : ℕ) = 1 then
      (if u ⟨⟨0, by omega⟩, mem_univ _⟩ then coin (4 / 5) (by norm_num) (by norm_num)
        else coin (1 / 5) (by norm_num) (by norm_num))
    else
      (if u ⟨⟨1, by omega⟩, mem_univ _⟩ then
        (if u ⟨⟨0, by omega⟩, mem_univ _⟩ then coin (9 / 10) (by norm_num) (by norm_num)
          else coin (1 / 2) (by norm_num) (by norm_num))
      else
        (if u ⟨⟨0, by omega⟩, mem_univ _⟩ then coin (1 / 2) (by norm_num) (by norm_num)
          else coin (1 / 10) (by norm_num) (by norm_num)))

/-- After `do(X = true)`, an assignment with `X = false` has probability `0`. -/
example : (confNet.intervene 1 true).joint ![true, false, true] = 0 := by
  rw [BayesNet.joint_intervene]
  simp

/-- After `do(X = true)`, `P(Z = true, X = true, Y = true) = P(Z = true) P(Y = true | X, Z)`
`= 1/2 · 9/10`: the table of `X` is dropped. -/
example : (confNet.intervene 1 true).joint ![true, true, true] = 9 / 20 := by
  rw [BayesNet.joint_intervene, show univ.erase (1 : Fin 3) = {0, 2} by decide,
    prod_pair (by decide)]
  simp [confNet, BayesNet.paVal, coin_true]
  norm_num

/-- **Non-vacuity** of the adjustment theorem: every table of `confNet` gives `X = true`
positive probability, so `E[f | do(X = true)]` is given by adjusting for `Z`. -/
example (f : (Fin 3 → Bool) → ℝ) :
    ∑ x, (confNet.intervene 1 true).joint x * f x =
      ∑ z : confNet.pa 1 → Bool, (∑ x with confNet.paVal 1 x = z, confNet.joint x) *
        ((∑ x with x 1 = true ∧ confNet.paVal 1 x = z, confNet.joint x * f x) /
          ∑ x with x 1 = true ∧ confNet.paVal 1 x = z, confNet.joint x) := by
  refine confNet.sum_intervene_joint_mul_of_cpt_ne_zero 1 true f fun z => ?_
  simp only [confNet]
  split_ifs <;> simp [coin_true]

/-- **Non-vacuity** of the back-door adjustment for predecessors: `Z = {0}` precedes `X` (node 1)
and contains its parent. -/
example (f : (Fin 3 → Bool) → ℝ) :
    ∑ x, (confNet.intervene 1 true).joint x * f x =
      ∑ z : ({0} : Finset (Fin 3)) → Bool,
        (∑ x with (fun i : ({0} : Finset (Fin 3)) => x i) = z, confNet.joint x) *
        ((∑ x with x 1 = true ∧ (fun i : ({0} : Finset (Fin 3)) => x i) = z,
            confNet.joint x * f x) /
          ∑ x with x 1 = true ∧ (fun i : ({0} : Finset (Fin 3)) => x i) = z, confNet.joint x) := by
  refine confNet.sum_intervene_joint_mul_of_pred_of_cpt_ne_zero 1 true {0}
    (fun i hi => by simp at hi; subst hi; decide) (fun j _ => ?_) f fun u => ?_
  · simp [Fin.ext_iff]
  · simp only [confNet]
    split_ifs <;> simp [coin_true]

/-! ### d-separation -/

/-- The chain `0 → 1 → 2` (node `k` has parent `k - 1`). -/
noncomputable def chainNet : BayesNet Bool 3 where
  pa k := if h : (k : ℕ) = 0 then ∅ else {⟨k - 1, by omega⟩}
  cpt _ _ := StdSimplex.single true

/-- The collider `0 → 2 ← 1`. -/
noncomputable def colliderNet : BayesNet Bool 3 where
  pa k := if (k : ℕ) = 2 then univ else ∅
  cpt _ _ := StdSimplex.single true

/-- In the chain, conditioning on the middle node blocks the path `0, 1, 2`. -/
example : chainNet.PathBlocked {1} [0, 1, 2] := by
  refine ⟨0, by simp, Or.inr ⟨fun h => ?_, rfl⟩⟩
  obtain ⟨-, ⟨h21, -⟩⟩ := h
  simp at h21

/-- In the collider, conditioning on the collider opens the path `0, 2, 1` (Berkson's paradox):
`{2}` does not d-separate `0` from `1`. -/
example : ¬colliderNet.DSeparated {0} {1} {2} := by
  intro h
  have hpath : colliderNet.IsPath 0 1 [0, 2, 1] := by
    refine ⟨by decide, ?_, rfl, rfl⟩
    simp only [List.isChain_cons_cons, List.isChain_singleton, and_true]
    exact ⟨Or.inl ⟨by simp, by simp [colliderNet]⟩, Or.inr ⟨by simp, by simp [colliderNet]⟩⟩
  obtain ⟨i, hi, hb⟩ := h 0 rfl 1 rfl _ hpath
  have hi0 : i = 0 := by simp at hi; omega
  subst hi0
  rcases hb with ⟨-, -, hdesc⟩ | ⟨hnc, -⟩
  · exact hdesc 2 Relation.ReflTransGen.refl rfl
  · exact hnc ⟨⟨by simp, by simp [colliderNet]⟩, ⟨by simp, by simp [colliderNet]⟩⟩

end Cslib.MachineLearning.CausalBayesNetTests
