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
# Tail ideals are dense in the vanishing-at-infinity ideal

Let B be a nonunital complex C-star algebra, T=[1,∞), and J_n={f∈C_b(T,B):f(t)=0 for all t≥n},
for n∈ℕ. Put χ_n(t)=min(1,max(0,n-t)) and f_n(t)=(χ_n(t):ℂ)•f(t). The cutoff is 1 for t≤n-1
and 0 for t≥n. If f∈C₀(T,B), the tail-supported functions f_n approximate f in the supremum
norm. Consequently closure(⋃n J_n)=C₀(T,B), and the directed closed supremum of the J_n equals
this vanishing ideal.
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

/-- **Bounded function truncated by a tail cutoff.**

Let B be a nonunital complex C-star algebra, T=[1,∞), and J_n={f∈C_b(T,B):f(t)=0 for all t≥n},
for n∈ℕ. Put χ_n(t)=min(1,max(0,n-t)) and f_n(t)=(χ_n(t):ℂ)•f(t). The cutoff is 1 for t≤n-1
and 0 for t≥n. For f∈C_b(T,B), tailApprox n f is f_n, a bounded continuous function vanishing
for t≥n.
-/
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

/-- **Pointwise formula for a tail approximation.**

Let B be a nonunital complex C-star algebra, T=[1,∞), and J_n={f∈C_b(T,B):f(t)=0 for all t≥n},
for n∈ℕ. For f∈C_b(T,B) and t∈T, tailApprox n f t=((min(1,max(0,n-t)):ℝ):ℂ)•f(t).
-/
@[simp]
theorem tailApprox_apply (n : ℕ) (f : AsymptoticTime →ᵇ B) (t : AsymptoticTime) :
    tailApprox n f t =
      ((min 1 (max 0 ((n : ℝ) - (t : ℝ))) : ℝ) : ℂ) • f t := by
  rfl

/-- **Tail approximations belong to the tail ideal.**

Let B be a nonunital complex C-star algebra, T=[1,∞), and J_n={f∈C_b(T,B):f(t)=0 for all t≥n},
for n∈ℕ. Put χ_n(t)=min(1,max(0,n-t)) and f_n(t)=(χ_n(t):ℂ)•f(t). The cutoff is 1 for t≤n-1
and 0 for t≥n. For f∈C_b(T,B), tailApprox n f=f_n belongs to J_n.
-/
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

/-- **Uniform approximation of a function vanishing at infinity.**

Let B be a nonunital complex C-star algebra, T=[1,∞), and J_n={f∈C_b(T,B):f(t)=0 for all t≥n},
for n∈ℕ. Put χ_n(t)=min(1,max(0,n-t)) and f_n(t)=(χ_n(t):ℂ)•f(t). The cutoff is 1 for t≤n-1
and 0 for t≥n. If f∈C₀(T,B) and ε>0, there exists n∈ℕ with ‖tailApprox n f-f‖∞<ε.
-/
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

/-- **Closure of the union of tail ideals.**

Let B be a nonunital complex C-star algebra, T=[1,∞), and J_n={f∈C_b(T,B):f(t)=0 for all t≥n},
for n∈ℕ. In C_b(T,B) with its supremum norm, closure(⋃n∈ℕ J_n)=C₀(T,B).
-/
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

/-- **Directed closed supremum of the tail ideals.**

Let B be a nonunital complex C-star algebra, T=[1,∞), and J_n={f∈C_b(T,B):f(t)=0 for all t≥n},
for n∈ℕ. The directed supremum of J_n in the lattice of closed star ideals of C_b(T,B) equals
C₀(T,B).
-/
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
