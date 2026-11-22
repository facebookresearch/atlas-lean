/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Convex.LagrangeDuality
public import MathlibExt.Analysis.Convex.FenchelMoreau
import Mathlib.Data.EReal.Operations
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The Lagrange dual function of linearly constrained problems via the conjugate

For the problem of minimizing `f₀ x` subject to linear inequality constraints
`aᵢ x ≤ bᵢ` (`i : ι` finite) on a real normed space, the Lagrange dual function is expressed
through the Fenchel conjugate `f₀*` of the objective:
`g(μ) = -∑ᵢ μᵢ bᵢ - f₀*(-∑ᵢ μᵢ aᵢ)` (Boyd–Vandenberghe §5.1.6, eq. (5.11), without equality
constraints). This is the bridge between conjugate functions and Lagrange duality: computing a
dual problem amounts to computing a conjugate.
-/

@[expose] public section

namespace MathlibExt.Analysis.Convex.DualViaConjugate

open LagrangeDuality FenchelMoreau

/-- Two extended reals with the same real lower bounds are equal. -/
private theorem eq_of_forall_coe_le_iff {u w : EReal}
    (h : ∀ p : ℝ, (p : EReal) ≤ u ↔ (p : EReal) ≤ w) : u = w := by
  refine le_antisymm ?_ ?_
  · by_contra huw
    push Not at huw
    obtain ⟨p, hwp, hpu⟩ := EReal.lt_iff_exists_real_btwn.1 huw
    exact absurd ((h p).1 hpu.le) (not_le.2 hwp)
  · by_contra huw
    push Not at huw
    obtain ⟨p, hup, hpw⟩ := EReal.lt_iff_exists_real_btwn.1 huw
    exact absurd ((h p).2 hpw.le) (not_le.2 hup)

private theorem coe_le_coe_sub_iff (c p : ℝ) (F : EReal) :
    (p : EReal) ≤ (c : EReal) - F ↔ F ≤ ((c - p : ℝ) : EReal) := by
  induction F using EReal.rec with
  | bot => simp
  | top => simpa using EReal.coe_ne_top (c - p)
  | coe r =>
    rw [← EReal.coe_sub, EReal.coe_le_coe_iff, EReal.coe_le_coe_iff]
    constructor <;> intro h <;> linarith

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]

/-- **The dual function of a linearly constrained problem is minus a conjugate.** For an objective
`f₀ : E → ℝ` on a real normed space and linear inequality constraints `aᵢ x - bᵢ ≤ 0` with
`aᵢ : E →L[ℝ] ℝ`, the Lagrange dual function over `D = E` is
`g(μ) = -∑ᵢ μᵢ bᵢ - f₀*(-∑ᵢ μᵢ aᵢ)`, where `f₀*` is the Fenchel conjugate (`fenchelConj`).

Source: S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University Press, 2004,
§5.1.6 ("The Lagrange dual function and conjugate functions"), eq. (5.11), without equality
constraints. -/
theorem dualFunction_linear_eq_neg_sub_fenchelConj (f₀ : E → ℝ) (a : ι → E →L[ℝ] ℝ)
    (b : ι → ℝ) (μ : ι → ℝ) :
    dualFunction Set.univ f₀ (fun i x => a i x - b i) μ =
      ((-∑ i, μ i * b i : ℝ) : EReal) -
        fenchelConj (fun x => ((f₀ x : ℝ) : EReal)) (-∑ i, μ i • a i) := by
  refine eq_of_forall_coe_le_iff fun p => ?_
  rw [coe_le_coe_sub_iff]
  unfold dualFunction fenchelConj
  simp only [Set.mem_univ, iInf_pos, le_iInf_iff, iSup_le_iff, EReal.coe_le_coe_iff]
  refine forall_congr' fun x => ?_
  rw [← EReal.coe_sub, EReal.coe_le_coe_iff]
  have hsum : (-∑ i, μ i • a i) x = -∑ i, μ i * a i x := by
    simp
  rw [hsum]
  unfold lagrangian
  have : ∑ i, μ i * (a i x - b i) = ∑ i, μ i * a i x - ∑ i, μ i * b i := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [this]
  constructor <;> intro h <;> linarith

end MathlibExt.Analysis.Convex.DualViaConjugate
