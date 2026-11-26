/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Statistics.LinearModel.FactorialOLS
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum

open Finset Matrix
open MathlibExt.Probability.Statistics.LinearModel

namespace MathlibExtTest.Probability.Statistics.LinearModel.FactorialOLS

-- The singleton column codes low as -1 and high as +1 in either replicate.
example (a : Fin 2) :
    factorialDesign 2 2 (![false, true], a) {0} = -1 ∧
    factorialDesign 2 2 (![true, false], a) {0} = 1 := by
  norm_num [factorialDesign, Fin.prod_univ_two]

-- The interaction sign is fixed by the treatment, independently of the replicate.
example (a : Fin 2) :
    factorialDesign 2 2 (![false, false], a) univ = 1 ∧
    factorialDesign 2 2 (![false, true], a) univ = -1 ∧
    factorialDesign 2 2 (![true, false], a) univ = -1 ∧
    factorialDesign 2 2 (![true, true], a) univ = 1 := by
  norm_num [factorialDesign, Fin.prod_univ_two]

-- Two factors with two replicates: the interaction partitions eight runs into two groups of four.
example :
    (univ.filter (fun x => factorialDesign 2 2 x univ = 1)).card = 4 ∧
    (univ.filter (fun x => factorialDesign 2 2 x univ = -1)).card = 4 := by
  have hn : (univ : Finset (Fin 2)) ≠ ∅ := by decide
  have h := (factorial_ols_effects (k := 2) (r := 2) (by decide) (fun _ => 0)).2.2.1 univ hn
  have hp := h.1
  have hm := h.2.1
  norm_num at hp hm
  constructor
  · exact_mod_cast (show ((univ.filter (fun x => factorialDesign 2 2 x univ = 1)).card : ℝ) = 4
      by linarith only [hp])
  · exact_mod_cast (show ((univ.filter (fun x => factorialDesign 2 2 x univ = -1)).card : ℝ) = 4
      by linarith only [hm])

-- A response of 7 on the positive interaction runs and 1 on the negative runs
-- gives an interaction coefficient of 3, not the conventional effect of 6.
example : olsEstimator (factorialDesign 2 2)
    (fun x => if factorialDesign 2 2 x univ = 1 then 7 else 1) univ = 3 := by
  let X := factorialDesign 2 2
  let y : ((Fin 2 → Bool) × Fin 2) → ℝ := fun x => if X x univ = 1 then 7 else 1
  let p := univ.filter fun x => X x univ = 1
  let n := univ.filter fun x => X x univ = -1
  have hn : (univ : Finset (Fin 2)) ≠ ∅ := by decide
  have h := (factorial_ols_effects (k := 2) (r := 2) (by decide) y).2.2.1 univ hn
  have hp : 2 * (p.card : ℝ) = 8 := by norm_num [p, X] at h ⊢; exact h.1
  have hm : 2 * (n.card : ℝ) = 8 := by norm_num [n, X] at h ⊢; exact h.2.1
  have hsp : (∑ x ∈ p, y x) = (p.card : ℝ) * 7 := by
    rw [← nsmul_eq_mul, ← sum_const]
    apply sum_congr rfl
    intro x hx
    have hx' : X x univ = 1 := (mem_filter.mp hx).2
    simp [y, hx']
  have hsn : (∑ x ∈ n, y x) = (n.card : ℝ) := by
    rw [← mul_one (n.card : ℝ), ← nsmul_eq_mul, ← sum_const]
    apply sum_congr rfl
    intro x hx
    have hx' : X x univ = -1 := (mem_filter.mp hx).2
    norm_num [y, hx']
  have hc := h.2.2.1
  change olsEstimator X y univ =
    ((∑ x ∈ p, y x) / (p.card : ℝ) - (∑ x ∈ n, y x) / (n.card : ℝ)) / 2 at hc
  rw [hsp, hsn, show (p.card : ℝ) = 4 by linarith, show (n.card : ℝ) = 4 by linarith] at hc
  norm_num at hc
  exact hc

-- With no factors, two replicate responses 1 and 5 have intercept 3.
example : olsEstimator (factorialDesign 0 2) (fun x => if x.2 = 0 then 1 else 5) ∅ = 3 := by
  rw [(factorial_ols_effects (k := 0) (r := 2) (by decide)
    (fun x => if x.2 = 0 then 1 else 5)).2.1]
  rw [Fintype.sum_prod_type_right]
  norm_num [Fin.sum_univ_two]

end MathlibExtTest.Probability.Statistics.LinearModel.FactorialOLS
