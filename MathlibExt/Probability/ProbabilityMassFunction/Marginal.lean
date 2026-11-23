/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Marginals of a finite joint probability mass function

For `p : PMF (α × β)` over finite types, the marginals `p.map Prod.fst` and
`p.map Prod.snd` are finite sums of `p` along the other coordinate, both as
`ℝ≥0∞` values and after `ENNReal.toReal`.
-/

@[expose] public section

namespace PMF

open scoped BigOperators ENNReal

variable {α β : Type*}

/-- The first marginal of a finite joint PMF is the sum over the second coordinate. -/
theorem map_fst_apply [Finite α] (p : PMF (α × β)) [Fintype β] (a : α) :
    (p.map Prod.fst) a = ∑ b, p (a, b) := by
  classical
  have := Fintype.ofFinite α
  rw [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type,
    Finset.sum_eq_single a (fun x _ hx ↦ by simp [Ne.symm hx]) (by simp)]
  simp

/-- The second marginal of a finite joint PMF is the sum over the first coordinate. -/
theorem map_snd_apply [Fintype α] [Finite β] (p : PMF (α × β)) (b : β) :
    (p.map Prod.snd) b = ∑ a, p (a, b) := by
  classical
  have := Fintype.ofFinite β
  rw [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type]
  simp

/-- `map_fst_apply` after `ENNReal.toReal`. -/
theorem toReal_map_fst_apply [Finite α] [Fintype β] (p : PMF (α × β)) (a : α) :
    ((p.map Prod.fst) a).toReal = ∑ b, (p (a, b)).toReal := by
  rw [map_fst_apply, ENNReal.toReal_sum fun b _ ↦ PMF.apply_ne_top p _]

/-- `map_snd_apply` after `ENNReal.toReal`. -/
theorem toReal_map_snd_apply [Fintype α] [Finite β] (p : PMF (α × β)) (b : β) :
    ((p.map Prod.snd) b).toReal = ∑ a, (p (a, b)).toReal := by
  rw [map_snd_apply, ENNReal.toReal_sum fun a _ ↦ PMF.apply_ne_top p _]

end PMF
