/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.CausalBayesNet
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Intervening differs from conditioning

In a confounded causal Bayesian network the interventional probability `P(Y | do(X = x))` and
the observational conditional probability `P(Y | X = x)` can differ: conditioning on `X = x`
also shifts the law of the confounder, while the intervention `do(X = x)` does not (Pearl 2009,
§3.2; Pearl, Glymour and Jewell 2016, §3.1).

## Main definitions

* `InterveningVsConditioning.confoundedNet`: the network `Z → X`, `Z → Y`, `X → Y` on `Bool`
  with rational tables.

## Main results

* `InterveningVsConditioning.confoundedNet_intervene`: `P(Y = true | do(X = true)) = 7/10`, by
  the truncated factorization `BayesNet.joint_intervene`.
* `InterveningVsConditioning.confoundedNet_cond`: `P(Y = true | X = true) = 41/50`.
* `InterveningVsConditioning.confoundedNet_intervene_ne_cond`: the two differ, and the
  conditioning event has positive probability.

## References

* J. Pearl, *Causality: Models, Reasoning, and Inference*, 2nd ed., Cambridge University Press
  (2009), §3.2.
* J. Pearl, M. Glymour and N. P. Jewell, *Causal Inference in Statistics: A Primer*, Wiley
  (2016), §3.1.
-/

@[expose] public section

namespace Cslib.MachineLearning.GraphicalModels
namespace InterveningVsConditioning

open Finset Convexity

/-- The distribution on `Bool` that is `true` with probability `p`. -/
noncomputable def coin (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : StdSimplex ℝ Bool :=
  StdSimplex.duple (t := 1 - p) true false h0 (by linarith) (by ring)

/-- The confounded network `Z → X`, `Z → Y`, `X → Y` on `Bool` (nodes `Z = 0`, `X = 1`,
`Y = 2`, each node's parents are all earlier nodes): `Z` is a fair coin; `X` is `true` with
probability `4/5` if `Z` and `1/5` otherwise; `Y` is `true` with probability `9/10`, `1/2`,
`1/2`, `1/10` for `(X, Z) = (true, true), (true, false), (false, true), (false, false)`. -/
noncomputable def confoundedNet : BayesNet Bool 3 where
  pa _ := univ
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

theorem coin_true (p : ℝ) (h0 h1) : (coin p h0 h1).weights true = p := by
  simp [coin, StdSimplex.duple]

theorem coin_false (p : ℝ) (h0 h1) : (coin p h0 h1).weights false = 1 - p := by
  simp [coin, StdSimplex.duple]

/-- A `Fin.snoc`-built assignment is the corresponding matrix literal. -/
lemma snoc3_eq (w : Fin 0 → Bool) (a b c : Bool) :
    Fin.snoc (Fin.snoc (Fin.snoc w a) b) c = (![a, b, c] : Fin 3 → Bool) := by
  funext i
  fin_cases i <;> rfl

/-- A sum over `Fin 3 → Bool` is the sum over the 8 explicit assignments. -/
lemma expand8 (f : (Fin 3 → Bool) → ℝ) :
    ∑ x, f x = f ![true, true, true] + f ![true, true, false] + f ![true, false, true] +
      f ![true, false, false] + f ![false, true, true] + f ![false, true, false] +
      f ![false, false, true] + f ![false, false, false] := by
  rw [sum_snoc]
  simp_rw [Fintype.sum_bool]
  rw [sum_snoc]
  simp_rw [Fintype.sum_bool]
  rw [sum_snoc]
  simp_rw [Fintype.sum_bool]
  rw [Fintype.sum_unique]
  simp only [snoc3_eq]
  ac_rfl

/-- `P(X = true) = 1/2` in the confounded network. -/
lemma sum_joint_x1 : ∑ x with x 1 = true, confoundedNet.joint x = 1 / 2 := by
  rw [Finset.sum_filter, expand8]
  simp_rw [BayesNet.joint_eq_prod]
  simp_rw [Fin.prod_univ_three]
  simp [confoundedNet, coin_true, coin_false]
  norm_num

/-- `P(X = true, Y = true) = 41/100` in the confounded network. -/
lemma sum_joint_x1y :
    ∑ x with x 1 = true ∧ x 2 = true, confoundedNet.joint x = 41 / 100 := by
  rw [Finset.sum_filter, expand8]
  simp_rw [BayesNet.joint_eq_prod]
  simp_rw [Fin.prod_univ_three]
  simp [confoundedNet, coin_true, coin_false]
  norm_num

/-- The interventional probability `P(Y = true | do(X = true)) = 1/2 · 9/10 + 1/2 · 1/2 = 7/10`
(the truncated factorization drops the table of `X`). -/
theorem confoundedNet_intervene : ∑ x with x 2 = true, (confoundedNet.intervene 1 true).joint x =
    7 / 10 := by
  rw [Finset.sum_filter, expand8]
  simp_rw [BayesNet.joint_intervene]
  simp_rw [show (univ.erase (1 : Fin 3)) = ({0, 2} : Finset (Fin 3)) from by decide]
  simp_rw [prod_pair (show (0 : Fin 3) ≠ 2 by decide)]
  simp [confoundedNet, BayesNet.paVal, coin_true, coin_false]
  norm_num

/-- The observational conditional probability
`P(Y = true | X = true) = P(X = true, Y = true) / P(X = true) = (41/100) / (1/2) = 41/50`. -/
theorem confoundedNet_cond :
    (∑ x with x 1 = true ∧ x 2 = true, confoundedNet.joint x) /
        ∑ x with x 1 = true, confoundedNet.joint x = 41 / 50 := by
  rw [sum_joint_x1y, sum_joint_x1]
  norm_num

/-- **Intervening differs from conditioning**: in the confounded network,
`P(Y = true | do(X = true)) ≠ P(Y = true | X = true)`; the conditioning event has positive
probability `P(X = true) = 1/2`. -/
theorem confoundedNet_intervene_ne_cond :
    0 < ∑ x with x 1 = true, confoundedNet.joint x ∧
      ∑ x with x 2 = true, (confoundedNet.intervene 1 true).joint x ≠
        (∑ x with x 1 = true ∧ x 2 = true, confoundedNet.joint x) /
          ∑ x with x 1 = true, confoundedNet.joint x := by
  refine ⟨?_, ?_⟩
  · rw [sum_joint_x1]
    norm_num
  · rw [confoundedNet_intervene, confoundedNet_cond]
    norm_num

end InterveningVsConditioning
end Cslib.MachineLearning.GraphicalModels
