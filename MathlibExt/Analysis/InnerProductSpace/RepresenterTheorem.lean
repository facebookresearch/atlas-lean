/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The representer theorem for ridge-regularized problems in Hilbert space

Given finitely many continuous linear functionals `L i : H →L[ℝ] ℝ` on a
real Hilbert space `H`, let `v i` be the Riesz representer of `L i`, so that
`L i x = ⟪v i, x⟫`. The **representer theorem** says that any minimizer of a
ridge-regularized problem

  `minimize F (fun i => L i g) + Λ * ‖g‖ ^ 2`

with `Λ > 0` lies in the finite-dimensional span of the representers `v i`.
In particular the infinite-dimensional problem reduces to a finite-dimensional
one: only the values `L i g` and the norm of `g` matter, and projecting `g`
orthogonally onto `span ℝ (range v)` preserves the values while not increasing
the norm.

This is the classical representer theorem for kernel methods (see e.g.
Schölkopf, Herbrich, and Smola, "A generalized representer theorem",
*COLT 2001*, Lecture Notes in Computer Science 2111, 2001, pp. 416–426;
the statement here is the Hilbert-space form underlying kernel ridge
regression). It is a companion to the Hilbert-space material of
`v1/Atlas/IntroductionToFunctionalAnalysis/code/HilbertSpace.lean`
(Riesz representation, orthogonal projection, Bessel's inequality) and to
the reproducing-kernel Hilbert space constructions in MathlibExt; it is not
one of the 72 v1 targets, and it is not in the pinned Mathlib or in base
MathlibExt.
-/

open scoped RealInnerProductSpace

@[expose] public section

namespace MathlibExt.Analysis.InnerProductSpace.RepresenterTheorem

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The Riesz representers of finitely many continuous linear functionals
span a finite-dimensional (hence complete) subspace. -/
private theorem completeSpace_span_range_toDual_symm {ι : Type*} [Fintype ι]
    (L : ι → (H →L[ℝ] ℝ)) :
    CompleteSpace
      (Submodule.span ℝ (Set.range fun i => (InnerProductSpace.toDual ℝ H).symm (L i))) := by
  have hSfin : FiniteDimensional ℝ
      (Submodule.span ℝ (Set.range fun i => (InnerProductSpace.toDual ℝ H).symm (L i))) :=
    (Submodule.fg_iff_finiteDimensional _).mp
      (Submodule.fg_span (Set.finite_range _))
  have : FiniteDimensional ℝ
      (Submodule.span ℝ (Set.range fun i => (InnerProductSpace.toDual ℝ H).symm (L i))) := hSfin
  exact completeSpace_coe_iff_isComplete.2
    (Submodule.span ℝ (Set.range fun i => (InnerProductSpace.toDual ℝ H).symm (L i))).complete_of_finiteDimensional

/-- Orthogonal projection onto the span of the Riesz representers preserves
the values of the functionals, and the Pythagorean identity holds for the
residual. -/
theorem exists_mem_span_norm_sq_add {ι : Type*} [Fintype ι]
    (L : ι → (H →L[ℝ] ℝ)) (g : H) :
    ∃ s ∈ Submodule.span ℝ (Set.range fun i => (InnerProductSpace.toDual ℝ H).symm (L i)),
      (∀ i, L i s = L i g) ∧ ‖g‖ ^ 2 = ‖s‖ ^ 2 + ‖g - s‖ ^ 2 := by
  classical
  set S := Submodule.span ℝ (Set.range fun i => (InnerProductSpace.toDual ℝ H).symm (L i)) with hS
  have := completeSpace_span_range_toDual_symm L
  obtain ⟨s, hsS, hws⟩ :=
    Submodule.HasOrthogonalProjection.exists_orthogonal (K := S) g
  refine ⟨s, hsS, fun i => ?_, ?_⟩
  · have hvi : (InnerProductSpace.toDual ℝ H).symm (L i) ∈ S := Submodule.subset_span ⟨i, rfl⟩
    have hLi : L i (g - s) = 0 := by
      have h := Submodule.inner_right_of_mem_orthogonal hvi hws
      rwa [InnerProductSpace.toDual_symm_apply] at h
    have h := map_sub (L i) g s
    rw [hLi] at h
    exact (sub_eq_zero.mp h.symm).symm
  · have hinner : ⟪s, g - s⟫ = 0 := Submodule.inner_right_of_mem_orthogonal hsS hws
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero s (g - s) hinner
    rw [add_sub_cancel] at h
    simp only [← pow_two] at h
    exact h

/-- Orthogonal projection onto the span of the Riesz representers does not
increase the norm. -/
theorem exists_mem_span_values_eq_norm_le {ι : Type*} [Fintype ι]
    (L : ι → (H →L[ℝ] ℝ)) (g : H) :
    ∃ s ∈ Submodule.span ℝ (Set.range fun i => (InnerProductSpace.toDual ℝ H).symm (L i)),
      (∀ i, L i s = L i g) ∧ ‖s‖ ≤ ‖g‖ := by
  obtain ⟨s, hsS, hvals, hnorm⟩ := exists_mem_span_norm_sq_add L g
  refine ⟨s, hsS, hvals, ?_⟩
  have hsq : ‖s‖ ^ 2 ≤ ‖g‖ ^ 2 := by
    rw [hnorm]
    exact le_add_of_nonneg_right (sq_nonneg _)
  calc ‖s‖ = Real.sqrt (‖s‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (‖g‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖g‖ := Real.sqrt_sq (norm_nonneg _)

/-- **Representer theorem.** Any minimizer of a ridge-regularized problem
`F (fun i => L i g) + Λ * ‖g‖ ^ 2` with `Λ > 0` lies in the span of the
Riesz representers of the functionals `L i`. -/
theorem mem_span_of_isMinOn {ι : Type*} [Fintype ι]
    (L : ι → (H →L[ℝ] ℝ)) (F : (ι → ℝ) → ℝ) {Λ : ℝ} (hΛ : 0 < Λ) {f : H}
    (hf : IsMinOn (fun g : H => F (fun i => L i g) + Λ * ‖g‖ ^ 2) Set.univ f) :
    f ∈ Submodule.span ℝ (Set.range fun i => (InnerProductSpace.toDual ℝ H).symm (L i)) := by
  obtain ⟨s, hsS, hvals, hnorm⟩ := exists_mem_span_norm_sq_add L f
  by_contra hfS
  have hne : f ≠ s := by
    rintro rfl
    exact hfS hsS
  have hwpos : 0 < ‖f - s‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne)) 2
  have hcost : F (fun i => L i f) + Λ * ‖f‖ ^ 2 ≤
      F (fun i => L i s) + Λ * ‖s‖ ^ 2 :=
    hf (Set.mem_univ s)
  have hFeq : F (fun i => L i f) = F (fun i => L i s) := by
    congr 1
    exact funext fun i => (hvals i).symm
  rw [hFeq, hnorm] at hcost
  nlinarith [hcost, hΛ, hwpos]

end MathlibExt.Analysis.InnerProductSpace.RepresenterTheorem
