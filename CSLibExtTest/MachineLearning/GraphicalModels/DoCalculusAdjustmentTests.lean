/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.DoCalculusAdjustment
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# The do-calculus derivation of the back-door formula, step by step

Exact values of each step of the derivation recorded in
`CSLibExt/MachineLearning/GraphicalModels/DoCalculusAdjustment.lean`, on the confounded network
`Z → X`, `Z → Y`, `X → Y` (nodes `0, 1, 2`) on `Bool`: total probability in the intervened
network (`P(Y = 1 | do(X = 1)) = 13/20`), rule 3 (`P(Z = z | do(X = 1)) = P(Z = z)`), rule 2
(`P(Y = 1 | do(X = 1), Z = z) = P(Y = 1 | X = 1, Z = z)`), and the resulting back-door value
`13/20`. These are computations with the truncated factorization, not a formalization of the
do-calculus.
-/

@[expose] public section

namespace Cslib.MachineLearning.DoCalculusAdjustmentTests

open Cslib.MachineLearning GraphicalModels Convexity Finset

/-- The distribution on `Bool` that is `true` with probability `p`. -/
noncomputable def coin (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : StdSimplex ℝ Bool :=
  StdSimplex.duple (t := 1 - p) true false h0 (by linarith) (by ring)

theorem coin_true (p : ℝ) (h0 h1) : (coin p h0 h1).weights true = p := by
  simp [coin, StdSimplex.duple]

theorem coin_false (p : ℝ) (h0 h1) : (coin p h0 h1).weights false = 1 - p := by
  simp [coin, StdSimplex.duple]

/-- The confounded network `Z → X`, `Z → Y`, `X → Y` (nodes `Z = 0`, `X = 1`, `Y = 2`, each
node's parents are all earlier nodes): `Z` is `true` with probability `1/4`; `X` is `true`
with probability `3/4` if `Z` and `1/4` otherwise; `Y` is `true` with probability `4/5`,
`3/5`, `2/5`, `1/5` for `(X, Z) = (true, true), (true, false), (false, true), (false, false)`. -/
noncomputable def net : BayesNet Bool 3 where
  pa _ := univ
  cpt k u := if h0 : (k : ℕ) = 0 then coin (1 / 4) (by norm_num) (by norm_num) else
    if h1 : (k : ℕ) = 1 then
      (if u ⟨⟨0, by omega⟩, mem_univ _⟩ then coin (3 / 4) (by norm_num) (by norm_num)
        else coin (1 / 4) (by norm_num) (by norm_num))
    else
      (if u ⟨⟨1, by omega⟩, mem_univ _⟩ then
        (if u ⟨⟨0, by omega⟩, mem_univ _⟩ then coin (4 / 5) (by norm_num) (by norm_num)
          else coin (3 / 5) (by norm_num) (by norm_num))
      else
        (if u ⟨⟨0, by omega⟩, mem_univ _⟩ then coin (2 / 5) (by norm_num) (by norm_num)
          else coin (1 / 5) (by norm_num) (by norm_num)))

theorem doj_ttt : (net.intervene 1 true).joint ![true, true, true] = 1 / 5 := by
  rw [BayesNet.joint_intervene, show univ.erase (1 : Fin 3) = {0, 2} by decide,
    prod_pair (by decide)]
  simp [net, BayesNet.paVal, coin_true]
  norm_num

theorem doj_ttf : (net.intervene 1 true).joint ![true, true, false] = 1 / 20 := by
  rw [BayesNet.joint_intervene, show univ.erase (1 : Fin 3) = {0, 2} by decide,
    prod_pair (by decide)]
  simp [net, BayesNet.paVal, coin_true, coin_false]
  norm_num

theorem doj_tft : (net.intervene 1 true).joint ![true, false, true] = 0 := by
  rw [BayesNet.joint_intervene]
  simp

theorem doj_tff : (net.intervene 1 true).joint ![true, false, false] = 0 := by
  rw [BayesNet.joint_intervene]
  simp

theorem doj_ftt : (net.intervene 1 true).joint ![false, true, true] = 9 / 20 := by
  rw [BayesNet.joint_intervene, show univ.erase (1 : Fin 3) = {0, 2} by decide,
    prod_pair (by decide)]
  simp [net, BayesNet.paVal, coin_true, coin_false]
  norm_num

theorem doj_ftf : (net.intervene 1 true).joint ![false, true, false] = 3 / 10 := by
  rw [BayesNet.joint_intervene, show univ.erase (1 : Fin 3) = {0, 2} by decide,
    prod_pair (by decide)]
  simp [net, BayesNet.paVal, coin_false]
  norm_num

theorem doj_fft : (net.intervene 1 true).joint ![false, false, true] = 0 := by
  rw [BayesNet.joint_intervene]
  simp

theorem doj_fff : (net.intervene 1 true).joint ![false, false, false] = 0 := by
  rw [BayesNet.joint_intervene]
  simp

theorem obs_ttt : net.joint ![true, true, true] = 3 / 20 := by
  rw [BayesNet.joint_eq_prod, Fin.prod_univ_three]
  simp [net, coin_true]
  norm_num

theorem obs_ttf : net.joint ![true, true, false] = 3 / 80 := by
  rw [BayesNet.joint_eq_prod, Fin.prod_univ_three]
  simp [net, coin_true, coin_false]
  norm_num

theorem obs_tft : net.joint ![true, false, true] = 1 / 40 := by
  rw [BayesNet.joint_eq_prod, Fin.prod_univ_three]
  simp [net, coin_true, coin_false]
  norm_num

theorem obs_tff : net.joint ![true, false, false] = 3 / 80 := by
  rw [BayesNet.joint_eq_prod, Fin.prod_univ_three]
  simp [net, coin_true, coin_false]
  norm_num

theorem obs_ftt : net.joint ![false, true, true] = 9 / 80 := by
  rw [BayesNet.joint_eq_prod, Fin.prod_univ_three]
  simp [net, coin_true, coin_false]
  norm_num

theorem obs_ftf : net.joint ![false, true, false] = 3 / 40 := by
  rw [BayesNet.joint_eq_prod, Fin.prod_univ_three]
  simp [net, coin_true, coin_false]
  norm_num

theorem obs_fft : net.joint ![false, false, true] = 9 / 80 := by
  rw [BayesNet.joint_eq_prod, Fin.prod_univ_three]
  simp [net, coin_true, coin_false]
  norm_num

theorem obs_fff : net.joint ![false, false, false] = 9 / 20 := by
  rw [BayesNet.joint_eq_prod, Fin.prod_univ_three]
  simp [net, coin_false]
  norm_num

theorem doj_sum_Y : ∑ x with x 2 = true, (net.intervene 1 true).joint x = 13 / 20 := by
  have hset : univ.filter (fun x : Fin 3 → Bool => x 2 = true) =
      {![true, true, true], ![true, false, true], ![false, true, true],
        ![false, false, true]} := by
    decide
  rw [hset, sum_insert (by decide), sum_insert (by decide), sum_insert (by decide),
    sum_singleton]
  simp only [doj_ttt, doj_tft, doj_ftt, doj_fft]
  norm_num

theorem doj_sum_Zt : ∑ x with x 0 = true, (net.intervene 1 true).joint x = 1 / 4 := by
  have hset : univ.filter (fun x : Fin 3 → Bool => x 0 = true) =
      {![true, true, true], ![true, true, false], ![true, false, true],
        ![true, false, false]} := by
    decide
  rw [hset, sum_insert (by decide), sum_insert (by decide), sum_insert (by decide),
    sum_singleton]
  simp only [doj_ttt, doj_ttf, doj_tft, doj_tff]
  norm_num

theorem doj_sum_Zf : ∑ x with x 0 = false, (net.intervene 1 true).joint x = 3 / 4 := by
  have hset : univ.filter (fun x : Fin 3 → Bool => x 0 = false) =
      {![false, true, true], ![false, true, false], ![false, false, true],
        ![false, false, false]} := by
    decide
  rw [hset, sum_insert (by decide), sum_insert (by decide), sum_insert (by decide),
    sum_singleton]
  simp only [doj_ftt, doj_ftf, doj_fft, doj_fff]
  norm_num

theorem doj_sum_ZYt :
    ∑ x with x 0 = true ∧ x 2 = true, (net.intervene 1 true).joint x = 1 / 5 := by
  have hset : univ.filter (fun x : Fin 3 → Bool => x 0 = true ∧ x 2 = true) =
      {![true, true, true], ![true, false, true]} := by
    decide
  rw [hset, sum_insert (by decide), sum_singleton]
  simp only [doj_ttt, doj_tft]
  norm_num

theorem doj_sum_ZYf :
    ∑ x with x 0 = false ∧ x 2 = true, (net.intervene 1 true).joint x = 9 / 20 := by
  have hset : univ.filter (fun x : Fin 3 → Bool => x 0 = false ∧ x 2 = true) =
      {![false, true, true], ![false, false, true]} := by
    decide
  rw [hset, sum_insert (by decide), sum_singleton]
  simp only [doj_ftt, doj_fft]
  norm_num

theorem obs_sum_Zt : ∑ x with x 0 = true, net.joint x = 1 / 4 := by
  have hset : univ.filter (fun x : Fin 3 → Bool => x 0 = true) =
      {![true, true, true], ![true, true, false], ![true, false, true],
        ![true, false, false]} := by
    decide
  rw [hset, sum_insert (by decide), sum_insert (by decide), sum_insert (by decide),
    sum_singleton]
  simp only [obs_ttt, obs_ttf, obs_tft, obs_tff]
  norm_num

theorem obs_sum_Zf : ∑ x with x 0 = false, net.joint x = 3 / 4 := by
  have hset : univ.filter (fun x : Fin 3 → Bool => x 0 = false) =
      {![false, true, true], ![false, true, false], ![false, false, true],
        ![false, false, false]} := by
    decide
  rw [hset, sum_insert (by decide), sum_insert (by decide), sum_insert (by decide),
    sum_singleton]
  simp only [obs_ftt, obs_ftf, obs_fft, obs_fff]
  norm_num

theorem obs_sum_ZXYt : ∑ x with x 0 = true ∧ x 1 = true ∧ x 2 = true, net.joint x = 3 / 20 := by
  have hset : univ.filter (fun x : Fin 3 → Bool => x 0 = true ∧ x 1 = true ∧ x 2 = true) =
      {![true, true, true]} := by
    decide
  rw [hset, sum_singleton]
  exact obs_ttt

theorem obs_sum_ZXYf :
    ∑ x with x 0 = false ∧ x 1 = true ∧ x 2 = true, net.joint x = 9 / 80 := by
  have hset : univ.filter (fun x : Fin 3 → Bool => x 0 = false ∧ x 1 = true ∧ x 2 = true) =
      {![false, true, true]} := by
    decide
  rw [hset, sum_singleton]
  exact obs_ftt

theorem obs_sum_ZXt : ∑ x with x 0 = true ∧ x 1 = true, net.joint x = 3 / 16 := by
  have hset : univ.filter (fun x : Fin 3 → Bool => x 0 = true ∧ x 1 = true) =
      {![true, true, true], ![true, true, false]} := by
    decide
  rw [hset, sum_insert (by decide), sum_singleton]
  simp only [obs_ttt, obs_ttf]
  norm_num

theorem obs_sum_ZXf : ∑ x with x 0 = false ∧ x 1 = true, net.joint x = 3 / 16 := by
  have hset : univ.filter (fun x : Fin 3 → Bool => x 0 = false ∧ x 1 = true) =
      {![false, true, true], ![false, true, false]} := by
    decide
  rw [hset, sum_insert (by decide), sum_singleton]
  simp only [obs_ftt, obs_ftf]
  norm_num

/-- Step 1 (probability axioms in the intervened model):
`P(Y = 1 | do(X = 1)) = ∑_z P(Z = z | do(X = 1)) P(Y = 1 | do(X = 1), Z = z)`, both sides
`= 13/20`. -/
theorem step1_total_probability :
    ∑ x with x 2 = true, (net.intervene 1 true).joint x =
      ∑ z : Bool, (∑ x with x 0 = z, (net.intervene 1 true).joint x) *
        ((∑ x with x 0 = z ∧ x 2 = true, (net.intervene 1 true).joint x) /
          ∑ x with x 0 = z, (net.intervene 1 true).joint x) ∧
    ∑ x with x 2 = true, (net.intervene 1 true).joint x = 13 / 20 := by
  refine ⟨?_, doj_sum_Y⟩
  simp only [Fintype.sum_bool, doj_sum_Y, doj_sum_Zt, doj_sum_Zf, doj_sum_ZYt, doj_sum_ZYf]
  norm_num

/-- Step 2 (rule 3, deleting the action: `Z` is not a descendant of `X`):
`P(Z = z | do(X = 1)) = P(Z = z)` for both values, `= 1/4` at `z = true`. -/
theorem step2_rule3 :
    (∀ z : Bool, ∑ x with x 0 = z, (net.intervene 1 true).joint x =
      ∑ x with x 0 = z, net.joint x) ∧
    ∑ x with x 0 = true, net.joint x = 1 / 4 := by
  refine ⟨?_, obs_sum_Zt⟩
  intro z
  cases z
  · rw [doj_sum_Zf, obs_sum_Zf]
  · rw [doj_sum_Zt, obs_sum_Zt]

/-- Step 3 (rule 2, exchanging action and observation: `Z` blocks the back-door path
`X ← Z → Y`): `P(Y = 1 | do(X = 1), Z = z) = P(Y = 1 | X = 1, Z = z)` for both values,
`= 4/5` at `z = true` and `3/5` at `z = false`. -/
theorem step3_rule2 :
    (∀ z : Bool,
      (∑ x with x 0 = z ∧ x 2 = true, (net.intervene 1 true).joint x) /
          ∑ x with x 0 = z, (net.intervene 1 true).joint x =
        (∑ x with x 0 = z ∧ x 1 = true ∧ x 2 = true, net.joint x) /
          ∑ x with x 0 = z ∧ x 1 = true, net.joint x) ∧
    (∑ x with x 0 = true ∧ x 1 = true ∧ x 2 = true, net.joint x) /
        ∑ x with x 0 = true ∧ x 1 = true, net.joint x = 4 / 5 ∧
    (∑ x with x 0 = false ∧ x 1 = true ∧ x 2 = true, net.joint x) /
        ∑ x with x 0 = false ∧ x 1 = true, net.joint x = 3 / 5 := by
  refine ⟨?_, ?_, ?_⟩
  · intro z
    cases z
    · rw [doj_sum_ZYf, doj_sum_Zf, obs_sum_ZXYf, obs_sum_ZXf]
      norm_num
    · rw [doj_sum_ZYt, doj_sum_Zt, obs_sum_ZXYt, obs_sum_ZXt]
      norm_num
  · rw [obs_sum_ZXYt, obs_sum_ZXt]
    norm_num
  · rw [obs_sum_ZXYf, obs_sum_ZXf]
    norm_num

/-- The end of the derivation, the back-door formula
`∑_z P(Z = z) P(Y = 1 | X = 1, Z = z)`, evaluated on the observational law: `13/20`, the value of
`P(Y = 1 | do(X = 1))` in `step1_total_probability`. -/
theorem backdoor_formula_value :
    ∑ z : Bool, (∑ x with x 0 = z, net.joint x) *
        ((∑ x with x 0 = z ∧ x 1 = true ∧ x 2 = true, net.joint x) /
          ∑ x with x 0 = z ∧ x 1 = true, net.joint x) = 13 / 20 := by
  simp only [Fintype.sum_bool, obs_sum_Zt, obs_sum_Zf, obs_sum_ZXYt, obs_sum_ZXYf,
    obs_sum_ZXt, obs_sum_ZXf]
  norm_num

end Cslib.MachineLearning.DoCalculusAdjustmentTests
