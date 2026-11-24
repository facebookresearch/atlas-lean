/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!
# Strong orthogonal sums identified by original scalar coefficients

This strict helper serves the actual computed normal-CFC PVM strong
countable-additivity field. Orthogonal star projections have a strong sum
by the existing projection theorem; scalar coefficient HasSum uniqueness
identifies its limit on the same original Hilbert space. No new norm,
separability, nontriviality or PVM model is installed.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped InnerProductSpace
namespace MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure
universe uH
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Actual orthogonal projection sums converge strongly to the bounded operator
whose original inner coefficients have the same sums. -/
theorem hasSum_of_orthogonal_of_inner_hasSum
    (P : ℕ → H →L[ℂ] H) (hP : ∀ n, IsStarProjection (P n))
    (horth : Pairwise fun i j => P i * P j = 0) (L : H →L[ℂ] H)
    (hcoeff : ∀ g h : H, HasSum (fun n => ⟪h, P n g⟫_ℂ) ⟪h, L g⟫_ℂ) :
    ∀ g : H, HasSum (fun n => P n g) (L g) := by
  obtain ⟨Q, _hQ, hsum, _hRange⟩ := exists_hasSum_of_pairwise_orthogonal P hP horth
  have heq : Q = L := by
    apply ContinuousLinearMap.ext
    intro g
    apply ext_inner_left ℂ
    intro h
    have hm := (hsum g).mapL (innerSL ℂ h)
    exact hm.unique (hcoeff g h)
  rw [← heq]
  exact hsum

end MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure

end
