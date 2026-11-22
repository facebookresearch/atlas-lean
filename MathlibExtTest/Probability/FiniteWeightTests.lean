/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.FiniteWeight
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

/-!
# Tests for marginals and conditional independence of finite weights

* Two perfectly correlated bits are not independent, so `CondIndep` is not vacuous.
* A product weight `f (x 0) * g (x 1)` makes the two bits independent, by the factorization
  criterion with `P = {0}`, `Q = {1}`.
* Conditional independence transfers to and from a marginal containing the variables involved.
-/

namespace MathlibExtTest.FiniteWeight

open MetaMathlibExt.FiniteWeight

/-- Two perfectly correlated bits. -/
noncomputable def copy (x : Fin 2 → Bool) : ℝ :=
  if x 0 = x 1 then 1 else 0

private theorem sum_fin_two_bool (f : (Fin 2 → Bool) → ℝ) :
    ∑ y, f y = f ![true, true] + f ![true, false] + (f ![false, true] + f ![false, false]) := by
  rw [← (piFinTwoEquiv fun _ => Bool).symm.sum_comp, Fintype.sum_prod_type, Fintype.sum_bool,
    Fintype.sum_bool, Fintype.sum_bool]
  rfl

example : ¬CondIndep copy {0} {1} ∅ := by
  intro h
  have := h ![true, false]
  simp only [marginal, Finset.sum_filter, sum_fin_two_bool] at this
  norm_num [copy] at this

example (f g : Bool → ℝ) : CondIndep (fun x : Fin 2 → Bool => f (x 0) * g (x 1)) {0} {1} ∅ := by
  have h := condIndep_of_dependsOn (f := fun x : Fin 2 → Bool => f (x 0))
    (g := fun x => g (x 1)) (P := {0}) (Q := {1}) (fun x y hxy => by simp [hxy 0 rfl])
    (fun x y hxy => by simp [hxy 1 rfl]) (fun v => by fin_cases v <;> simp)
    (A := {0}) (B := {1}) (by simp) (by simp)
  simp only [Set.inter_def] at h
  convert h using 1
  · ext v
    fin_cases v <;> simp

example (p : (Fin 4 → Bool) → ℝ) (h : CondIndep p {0} {1} {2}) :
    CondIndep (marginal p {0, 1, 2}) {0} {1} {2} :=
  (condIndep_marginal_iff (by simp) (by simp) (by simp)).mpr h

end MathlibExtTest.FiniteWeight
