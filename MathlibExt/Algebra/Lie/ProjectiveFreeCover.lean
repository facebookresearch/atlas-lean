/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Lie.Basic
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-!
# A free underlying Lie algebra retract of a projective Lie algebra

The projective module definition supplies a section of the canonical linear
combination map from `L →₀ R` to `L`. On a separate copy of this free module
the bracket is `i ⁅p x, p y⁆`. The section identity proves alternation,
Jacobi, and the Lie compatibility of both maps. The complement is central.

This construction uses projectivity over the original commutative ring.
It makes no assumption that the original module is free, and the free
carrier lives in the maximum of the original scalar and Lie universes.
-/

@[expose] public section

noncomputable section

universe u v

namespace LieAlgebra

variable (R : Type u) [CommRing R]
  (L : Type v) [LieRing L] [LieAlgebra R L]

/-- A separate carrier for the free module on the original Lie algebra.
Its Lie bracket is installed from the actual projective section below. -/
def ProjectiveFreeCover : Type (max u v) := L →₀ R

instance projectiveFreeCoverAddCommGroup : AddCommGroup (ProjectiveFreeCover R L) :=
  inferInstanceAs (AddCommGroup (L →₀ R))

instance projectiveFreeCoverModule : Module R (ProjectiveFreeCover R L) :=
  inferInstanceAs (Module R (L →₀ R))

/-- The underlying free module is the actual finitely supported function module. -/
def projectiveFreeCoverEquiv : ProjectiveFreeCover R L ≃ₗ[R] (L →₀ R) :=
  LinearEquiv.refl R (L →₀ R)

instance projectiveFreeCoverFree : Module.Free R (ProjectiveFreeCover R L) :=
  Module.Free.of_equiv (projectiveFreeCoverEquiv R L).symm

/-- The canonical original linear-combination projection. -/
def projectiveCoverLinearProjection : ProjectiveFreeCover R L →ₗ[R] L :=
  Finsupp.linearCombination R (id : L → L)

variable [hL : Module.Projective R L]

/-- The actual section supplied by projectivity of the original module. -/
def projectiveCoverLinearInclusion : L →ₗ[R] ProjectiveFreeCover R L :=
  Classical.choose hL.out

@[simp]
theorem projectiveCoverLinearProjection_inclusion_apply (x : L) :
    projectiveCoverLinearProjection R L (projectiveCoverLinearInclusion R L x) = x :=
  Classical.choose_spec hL.out x

@[simp]
theorem projectiveCoverLinearProjection_comp_inclusion :
    (projectiveCoverLinearProjection R L).comp (projectiveCoverLinearInclusion R L) =
      LinearMap.id := by
  apply LinearMap.ext
  exact projectiveCoverLinearProjection_inclusion_apply R L

/-- The bracket on the free underlying module is obtained from the original
bracket and the actual section/retraction, rather than stipulated by a
free-bracket extension hypothesis. -/
instance projectiveFreeCoverLieRing : LieRing (ProjectiveFreeCover R L) where
  __ := projectiveFreeCoverAddCommGroup R L
  bracket x y := projectiveCoverLinearInclusion R L
    ⁅projectiveCoverLinearProjection R L x, projectiveCoverLinearProjection R L y⁆
  add_lie x y z := by
    change projectiveCoverLinearInclusion R L
        ⁅projectiveCoverLinearProjection R L (x + y), projectiveCoverLinearProjection R L z⁆ = _
    rw [map_add, add_lie, map_add]
  lie_add x y z := by
    change projectiveCoverLinearInclusion R L
        ⁅projectiveCoverLinearProjection R L x, projectiveCoverLinearProjection R L (y + z)⁆ = _
    rw [map_add, lie_add, map_add]
  lie_self x := by
    change projectiveCoverLinearInclusion R L
      ⁅projectiveCoverLinearProjection R L x, projectiveCoverLinearProjection R L x⁆ = 0
    rw [lie_self, map_zero]
  leibniz_lie x y z := by
    change projectiveCoverLinearInclusion R L
        ⁅projectiveCoverLinearProjection R L x,
          projectiveCoverLinearProjection R L (projectiveCoverLinearInclusion R L
            ⁅projectiveCoverLinearProjection R L y, projectiveCoverLinearProjection R L z⁆)⁆ =
      projectiveCoverLinearInclusion R L
        ⁅projectiveCoverLinearProjection R L (projectiveCoverLinearInclusion R L
            ⁅projectiveCoverLinearProjection R L x, projectiveCoverLinearProjection R L y⁆),
          projectiveCoverLinearProjection R L z⁆ +
        projectiveCoverLinearInclusion R L
          ⁅projectiveCoverLinearProjection R L y,
            projectiveCoverLinearProjection R L (projectiveCoverLinearInclusion R L
              ⁅projectiveCoverLinearProjection R L x, projectiveCoverLinearProjection R L z⁆)⁆
    rw [projectiveCoverLinearProjection_inclusion_apply,
      projectiveCoverLinearProjection_inclusion_apply,
      projectiveCoverLinearProjection_inclusion_apply, leibniz_lie, map_add]

instance projectiveFreeCoverLieAlgebra : LieAlgebra R (ProjectiveFreeCover R L) where
  __ := projectiveFreeCoverModule R L
  lie_smul r x y := by
    change projectiveCoverLinearInclusion R L
        ⁅projectiveCoverLinearProjection R L x, projectiveCoverLinearProjection R L (r • y)⁆ =
      r • projectiveCoverLinearInclusion R L
        ⁅projectiveCoverLinearProjection R L x, projectiveCoverLinearProjection R L y⁆
    rw [map_smul, lie_smul, map_smul]

@[simp]
theorem projectiveFreeCover_lie (x y : ProjectiveFreeCover R L) :
    ⁅x, y⁆ = projectiveCoverLinearInclusion R L
      ⁅projectiveCoverLinearProjection R L x, projectiveCoverLinearProjection R L y⁆ := rfl

/-- The projective section is an actual Lie algebra homomorphism for the
constructed bracket. -/
def projectiveCoverInclusion : L →ₗ⁅R⁆ ProjectiveFreeCover R L where
  toLinearMap := projectiveCoverLinearInclusion R L
  map_lie' := by
    intro x y
    change projectiveCoverLinearInclusion R L ⁅x, y⁆ =
      projectiveCoverLinearInclusion R L
        ⁅projectiveCoverLinearProjection R L (projectiveCoverLinearInclusion R L x),
          projectiveCoverLinearProjection R L (projectiveCoverLinearInclusion R L y)⁆
    rw [projectiveCoverLinearProjection_inclusion_apply,
      projectiveCoverLinearProjection_inclusion_apply]

/-- The canonical projection is an actual Lie algebra homomorphism. -/
def projectiveCoverProjection : ProjectiveFreeCover R L →ₗ⁅R⁆ L where
  toLinearMap := projectiveCoverLinearProjection R L
  map_lie' := by
    intro x y
    change projectiveCoverLinearProjection R L (projectiveCoverLinearInclusion R L
      ⁅projectiveCoverLinearProjection R L x, projectiveCoverLinearProjection R L y⁆) = _
    exact projectiveCoverLinearProjection_inclusion_apply R L _

@[simp]
theorem projectiveCoverProjection_inclusion_apply (x : L) :
    projectiveCoverProjection R L (projectiveCoverInclusion R L x) = x :=
  by
    change projectiveCoverLinearProjection R L (projectiveCoverLinearInclusion R L x) = x
    exact projectiveCoverLinearProjection_inclusion_apply R L x

@[simp]
theorem projectiveCoverProjection_comp_inclusion :
    (projectiveCoverProjection R L).comp (projectiveCoverInclusion R L) = LieHom.id := by
  apply LieHom.ext
  exact projectiveCoverProjection_inclusion_apply R L

/-- The complement introduced by the free cover is central. -/
theorem projectiveFreeCover_lie_eq_zero_of_projection_eq_zero
    (x y : ProjectiveFreeCover R L) (hx : projectiveCoverProjection R L x = 0) :
    ⁅x, y⁆ = 0 := by
  rw [projectiveFreeCover_lie]
  have hx' : projectiveCoverLinearProjection R L x = 0 := hx
  rw [hx', zero_lie, map_zero]

/-- The free cover has the usual single-one basis, without a finite-rank assumption. -/
def projectiveFreeCoverBasis : Module.Basis L R (ProjectiveFreeCover R L) :=
  Finsupp.basisSingleOne

end LieAlgebra
