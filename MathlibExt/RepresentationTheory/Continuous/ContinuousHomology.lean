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

public import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic
public import MathlibExt.Algebra.Category.ModuleCat.Topology.Homology

/-!
# Concrete representatives and boundaries in continuous cohomology

In every positive degree, the homology projection from homogeneous continuous
cocycles is surjective.  A cocycle represents zero exactly when its included
cochain is the differential of a cochain in the predecessor degree.

These statements only assert existence through the concrete quotient model;
they do not choose representatives naturally.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory TopRep

universe u v w

namespace ContinuousCohomology

variable {k : Type u} {G : Type v} [Ring k] [TopologicalSpace k]
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Every positive-degree continuous cohomology class has a homogeneous
continuous cocycle representative.  No natural choice is asserted. -/
theorem π_surjective_succ (X : TopRep.{max v w} k G) (n : ℕ) :
    Function.Surjective (π.{u, v, w} X (n + 1)) := by
  let K := TopRep.homogeneousCochains.{u, v, w} X
  have hPrev : (ComplexShape.up ℕ).prev (n + 1) = n :=
    (ComplexShape.up ℕ).prev_eq' rfl
  exact K.homologyπ_surjective n (n + 1) hPrev

/-- A positive-degree homogeneous continuous cocycle represents zero exactly
when its included cochain is an explicit predecessor-degree boundary. -/
theorem π_eq_zero_iff_exists_boundary_succ
    (X : TopRep.{max v w} k G) (n : ℕ)
    (z : cocycles.{u, v, w} X (n + 1)) :
    π.{u, v, w} X (n + 1) z = 0 ↔
      ∃ b : (TopRep.homogeneousCochains.{u, v, w} X).X n,
        ((TopRep.homogeneousCochains.{u, v, w} X).iCycles
          (n + 1)).hom z =
          ((TopRep.homogeneousCochains.{u, v, w} X).d n
            (n + 1)).hom b := by
  let K := TopRep.homogeneousCochains.{u, v, w} X
  have hPrev : (ComplexShape.up ℕ).prev (n + 1) = n :=
    (ComplexShape.up ℕ).prev_eq' rfl
  exact K.homologyπ_eq_zero_iff_exists_boundary n (n + 1) hPrev z

end ContinuousCohomology
