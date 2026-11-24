/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.Analysis.CStarAlgebra.AsymptoticMorphism.TailIdeals
public import MathlibExt.Analysis.CStarAlgebra.IdealQuotient.DirectedSup

import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Tactic.Linarith

/-!
# The directed tail closure is the actual C0 ideal

The explicit private scalar cutoff min1(max0(n-t)) is bounded by1,
equal1 before n-1 and zero from n on. Multiplication of an actual BCF by
this scalar yields a true member of J_n. The real atTop vanishing property
gives sup-norm approximation, proving closure(unionJ_n)=C0.

No approximation, closure equality, limit ideal or lifting output is assumed.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Filter
open scoped ZeroAtInfty BoundedContinuousFunction

noncomputable section

namespace AsymptoticAlgebra

universe uB

private def tailCutoff (n : ℕ) (t : AsymptoticTime) : ℝ :=
  min 1 (max 0 ((n : ℝ) - (t : ℝ)))

private theorem tailCutoff_bounds (n : ℕ) (t : AsymptoticTime) :
    0 ≤ tailCutoff n t ∧ tailCutoff n t ≤ 1 :=
  ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩

private theorem tailCutoff_continuous (n : ℕ) : Continuous (tailCutoff n) := by
  have hsub : Continuous (fun t : AsymptoticTime => (n : ℝ) - (t : ℝ)) :=
    continuous_const.fun_sub continuous_subtype_val
  exact continuous_const.min (continuous_const.max hsub)

private theorem tailCutoff_zero (n : ℕ) (t : AsymptoticTime)
    (ht : (n : ℝ) ≤ (t : ℝ)) : tailCutoff n t = 0 := by
  rw [tailCutoff, max_eq_left (sub_nonpos.mpr ht), min_eq_right zero_le_one]

private theorem tailCutoff_one (n : ℕ) (t : AsymptoticTime)
    (ht : (t : ℝ) ≤ (n : ℝ) - 1) : tailCutoff n t = 1 := by
  have h1 : 1 ≤ (n : ℝ) - (t : ℝ) := by linarith
  rw [tailCutoff, min_eq_left (h1.trans (le_max_right _ _))]

variable {B : Type uB} [NonUnitalCStarAlgebra B]

private theorem norm_tailCutoff_smul_le (n : ℕ) (t : AsymptoticTime) (b : B) :
    ‖(tailCutoff n t : ℂ) • b‖ ≤ ‖b‖ := by
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (tailCutoff_bounds n t).1]
  calc
    tailCutoff n t * ‖b‖ ≤ 1 * ‖b‖ :=
      mul_le_mul_of_nonneg_right (tailCutoff_bounds n t).2 (norm_nonneg b)
    _ = ‖b‖ := one_mul _

/-- A computed bounded tail-supported approximation in the STOCK function norm. -/
@[no_expose]
def tailApprox (n : ℕ) (f : AsymptoticTime →ᵇ B) : AsymptoticTime →ᵇ B where
  toFun t := (tailCutoff n t : ℂ) • f t
  continuous_toFun :=
    (Complex.continuous_ofReal.comp (tailCutoff_continuous n)).fun_smul f.continuous
  map_bounded' := by
    refine ⟨‖f‖ + ‖f‖, fun s t => ?_⟩
    apply (dist_le_norm_add_norm _ _).trans
    exact add_le_add
      ((norm_tailCutoff_smul_le n s (f s)).trans (f.norm_coe_le_norm s))
      ((norm_tailCutoff_smul_le n t (f t)).trans (f.norm_coe_le_norm t))

/-- The public pointwise formula does not expose any private cutoff/proof name. -/
@[simp]
theorem tailApprox_apply (n : ℕ) (f : AsymptoticTime →ᵇ B) (t : AsymptoticTime) :
    tailApprox n f t =
      ((min 1 (max 0 ((n : ℝ) - (t : ℝ))) : ℝ) : ℂ) • f t := by
  rfl

/-- The concrete approximation belongs to the exact source J_n. -/
theorem tailApprox_mem (n : ℕ) (f : AsymptoticTime →ᵇ B) :
    tailApprox n f ∈ tailIdeal n B := by
  apply (mem_tailIdeal_iff n _).2
  intro t ht
  change (tailCutoff n t : ℂ) • f t = 0
  rw [tailCutoff_zero n t ht, Complex.ofReal_zero, zero_smul]

theorem tailApprox_eq_of_le (n : ℕ) (f : AsymptoticTime →ᵇ B)
    (t : AsymptoticTime) (ht : (t : ℝ) ≤ (n : ℝ) - 1) :
    tailApprox n f t = f t := by
  change (tailCutoff n t : ℂ) • f t = f t
  rw [tailCutoff_one n t ht, Complex.ofReal_one, one_smul]

private theorem tailApprox_error_le (n : ℕ) (f : AsymptoticTime →ᵇ B)
    (t : AsymptoticTime) : ‖tailApprox n f t - f t‖ ≤ ‖f t‖ := by
  have heq : tailApprox n f t - f t = ((tailCutoff n t : ℂ) - 1) • f t := by
    change (tailCutoff n t : ℂ) • f t - f t = _
    rw [sub_smul, one_smul]
  rw [heq, norm_smul]
  have hc : ‖(tailCutoff n t : ℂ) - 1‖ ≤ 1 := by
    have heq : (tailCutoff n t : ℂ) - 1 = ((tailCutoff n t - 1 : ℝ) : ℂ) := by
      rw [Complex.ofReal_sub, Complex.ofReal_one]
    rw [heq, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (sub_nonpos.mpr (tailCutoff_bounds n t).2)]
    have hnonneg := (tailCutoff_bounds n t).1
    linarith
  calc
    ‖(tailCutoff n t : ℂ) - 1‖ * ‖f t‖ ≤ 1 * ‖f t‖ :=
      mul_le_mul_of_nonneg_right hc (norm_nonneg _)
    _ = ‖f t‖ := one_mul _

/-- C0 vanishing produces actual members of J_n arbitrarily close in sup norm. -/
theorem exists_tailApprox_close (f : AsymptoticTime →ᵇ B)
    (hf : f ∈ BoundedContinuousFunction.vanishingIdeal AsymptoticTime B)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, ‖tailApprox n f - f‖ < ε := by
  let : Nonempty AsymptoticTime := ⟨⟨1, le_rfl⟩⟩
  have htendsto := (mem_vanishingIdeal_iff f).1 hf
  have hsmall : ∀ᶠ t : AsymptoticTime in atTop, ‖f t‖ < ε / 2 := by
    simpa only [dist_zero_right] using
      Metric.tendsto_nhds.mp htendsto (ε / 2) (half_pos hε)
  obtain ⟨r, hr⟩ := Filter.mem_atTop_sets.mp hsmall
  obtain ⟨n, hn⟩ := exists_nat_gt ((r : ℝ) + 1)
  have hnlarge : (r : ℝ) < (n : ℝ) - 1 := by linarith
  have hnorm : ‖tailApprox n f - f‖ ≤ ε / 2 := by
    apply (BoundedContinuousFunction.norm_le (half_pos hε).le).2
    intro t
    rw [BoundedContinuousFunction.sub_apply]
    by_cases ht : (t : ℝ) ≤ (n : ℝ) - 1
    · rw [tailApprox_eq_of_le n f t ht, sub_self, norm_zero]
      exact (half_pos hε).le
    · have htail : r ≤ t := hnlarge.le.trans (le_of_not_ge ht)
      exact (tailApprox_error_le n f t).trans (hr t htail).le
  exact ⟨n, hnorm.trans_lt (half_lt_self hε)⟩

/-- Literal closed-union identity, preserving the original C0 carrier. -/
theorem closure_iUnion_tailIdeal (B : Type uB) [NonUnitalCStarAlgebra B] :
    closure (⋃ n : ℕ, (tailIdeal n B : Set (AsymptoticTime →ᵇ B))) =
      (BoundedContinuousFunction.vanishingIdeal AsymptoticTime B :
        Set (AsymptoticTime →ᵇ B)) := by
  apply le_antisymm
  · exact closure_minimal
      (Set.iUnion_subset fun n => tailIdeal_le_vanishingIdeal n B)
      (BoundedContinuousFunction.vanishingIdeal AsymptoticTime B).isClosed
  · intro f hf
    apply Metric.mem_closure_iff.2
    intro ε hε
    obtain ⟨n, hn⟩ := exists_tailApprox_close f hf ε hε
    refine ⟨tailApprox n f, Set.mem_iUnion.mpr ⟨n, tailApprox_mem n f⟩, ?_⟩
    calc
      dist f (tailApprox n f) = dist (tailApprox n f) f := dist_comm _ _
      _ = ‖tailApprox n f - f‖ := dist_eq_norm _ _
      _ < ε := hn

/-- The independently constructed directed closed supremum IS the concrete C0 ideal. -/
theorem directedSup_tailIdeal (B : Type uB) [NonUnitalCStarAlgebra B] :
    ClosedStarIdeal.directedSup (fun n : ℕ => tailIdeal n B) (tailIdeal_directed B) =
      BoundedContinuousFunction.vanishingIdeal AsymptoticTime B := by
  apply SetLike.coe_injective
  calc
    (ClosedStarIdeal.directedSup (fun n : ℕ => tailIdeal n B)
        (tailIdeal_directed B) : Set (AsymptoticTime →ᵇ B)) =
      closure (⋃ n : ℕ, (tailIdeal n B : Set (AsymptoticTime →ᵇ B))) :=
        ClosedStarIdeal.directedSup_carrier _ _
    _ = _ := closure_iUnion_tailIdeal B

end AsymptoticAlgebra
