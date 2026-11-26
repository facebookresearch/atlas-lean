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
# Representatives and boundaries in positive continuous cohomology

Let G be a topological group and X a topological representation over a topological ring k. In
degree n+1, the continuous-cohomology projection from homogeneous cycles is surjective. A
cycle has zero class precisely when its included cochain is the differential of a degree-n
cochain.

These are statements about the concrete quotient of cycles by boundaries, with the group and
coefficient universe levels specified independently.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory TopRep

universe u v w

namespace ContinuousCohomology

variable {k : Type u} {G : Type v} [Ring k] [TopologicalSpace k]
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Surjectivity of the positive-degree homology projection.

For every n ≥ 0 and topological representation X, each class in continuous Hⁿ⁺¹(G,X) has a
homogeneous continuous cycle representative. -/
theorem π_surjective_succ (X : TopRep.{max v w} k G) (n : ℕ) :
    Function.Surjective (π.{u, v, w} X (n + 1)) := by
  let K := TopRep.homogeneousCochains.{u, v, w} X
  have hPrev : (ComplexShape.up ℕ).prev (n + 1) = n :=
    (ComplexShape.up ℕ).prev_eq' rfl
  exact K.homologyπ_surjective n (n + 1) hPrev

/-- Zero classes are predecessor-degree boundaries.

For a homogeneous continuous cycle z in degree n+1, its class is zero if and only if there is
a cochain b in degree n such that the included cochain of z equals dⁿb. -/
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
