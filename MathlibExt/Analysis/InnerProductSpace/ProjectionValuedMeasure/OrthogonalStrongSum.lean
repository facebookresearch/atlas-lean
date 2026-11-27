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
# Strong orthogonal sums from scalar coefficient sums

Let `H` be a complete complex Hilbert space and `P_n` orthogonal projections with pairwise
orthogonal ranges. If a bounded operator `L` satisfies `Σ_n ⟨h,P_n g⟩=⟨h,Lg⟩` for every `g,h ∈
H`, then `Σ_n P_n g=Lg` in the Hilbert norm for every `g`.

This identifies the strong sum by all its scalar coefficients. No separability,
finite-dimensionality or nonzero-space condition is needed.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped InnerProductSpace
namespace MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure
universe uH
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Strong sum determined by orthogonal scalar coefficients.** Let `H` be a complete complex
Hilbert space, `P_n` orthogonal projections with `P_i P_j=0` for `i≠j`, and `L : H →L[ℂ]
H`. If the scalar series `Σ_n ⟨h,P_n g⟩` has sum `⟨h,Lg⟩` for every `g,h ∈ H`, then the
vector series `Σ_n P_n g` has sum `Lg` in the Hilbert norm for every `g`. -/
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
