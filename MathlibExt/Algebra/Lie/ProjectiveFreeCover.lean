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
# A free-module Lie cover of a projective Lie algebra

Let R be a commutative ring and L an R-Lie algebra whose underlying
R-module is projective. The free R-module F = L →₀ R has the canonical
projection p(∑_x r_x δ_x) = ∑_x r_x x. Projectivity supplies an R-linear
section s : L → F with p s = id_L.

Give F the Lie bracket [u,v]_F = s([p(u),p(v)]_L). Then F is an
R-Lie algebra, s and p are Lie homomorphisms, and p s = id as Lie maps.
The kernel of p is central, since [u,v]_F = 0 when p(u) = 0.
Thus L is a Lie retract of an algebra whose underlying module is free.
Its module basis is δ_x, x ∈ L, and its carrier lies in max(u,v)
for the independent worlds of R and L.
-/

@[expose] public section

noncomputable section

universe u v

namespace LieAlgebra

variable (R : Type u) [CommRing R]
  (L : Type v) [LieRing L] [LieAlgebra R L]

/-- For a commutative ring R and an R-Lie algebra L, the free
cover carrier is F = L →₀ R, the finitely supported R-valued
functions on L. Its world is max(u,v), where R and L have
independent carrier worlds u and v. Its module basis is indexed
by the elements of L. -/
def ProjectiveFreeCover : Type (max u v) := L →₀ R

instance projectiveFreeCoverAddCommGroup : AddCommGroup (ProjectiveFreeCover R L) :=
  inferInstanceAs (AddCommGroup (L →₀ R))

instance projectiveFreeCoverModule : Module R (ProjectiveFreeCover R L) :=
  inferInstanceAs (Module R (L →₀ R))

/-- For a commutative ring R and an R-Lie algebra L, the
underlying cover module F is R-linearly equivalent to L →₀ R
by the identity on finitely supported coefficient functions. -/
def projectiveFreeCoverEquiv : ProjectiveFreeCover R L ≃ₗ[R] (L →₀ R) :=
  LinearEquiv.refl R (L →₀ R)

omit [LieRing L] [LieAlgebra R L] in
/-- The canonical cover equivalence retains every coefficient of the finitely supported vector. -/
@[simp]
theorem projectiveFreeCoverEquiv_apply (x : ProjectiveFreeCover R L) :
    projectiveFreeCoverEquiv R L x = (x : L →₀ R) := rfl

omit [LieRing L] [LieAlgebra R L] in
/-- The inverse cover equivalence retains every coefficient of the finitely supported vector. -/
@[simp]
theorem projectiveFreeCoverEquiv_symm_apply (x : L →₀ R) :
    (projectiveFreeCoverEquiv R L).symm x = (x : ProjectiveFreeCover R L) := rfl

instance projectiveFreeCoverFree : Module.Free R (ProjectiveFreeCover R L) :=
  Module.Free.of_equiv (projectiveFreeCoverEquiv R L).symm

/-- For a commutative ring R and an R-Lie algebra L, the
R-linear projection p : (L →₀ R) → L sends a finitely supported
family c to ∑_x c(x) • x. In particular p(δ_x) = x. -/
def projectiveCoverLinearProjection : ProjectiveFreeCover R L →ₗ[R] L :=
  Finsupp.linearCombination R (id : L → L)

variable [hL : Module.Projective R L]

/-- For a commutative ring R and an R-Lie algebra L whose
underlying R-module is projective, the canonical projection
p : (L →₀ R) → L has an R-linear section s : L → (L →₀ R)
satisfying p(s(x)) = x for every x ∈ L. -/
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

/-- For a projective R-Lie algebra L over a commutative ring R,
let p : F → L and s : L → F be the canonical free-cover projection
and its projective section, with p s = id. The bracket
[u,v]_F = s([p(u),p(v)]_L) makes the additive group F = L →₀ R
a Lie ring. -/
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

/-- For an R-Lie algebra L projective as an R-module, give
F = L →₀ R the bracket [u,v]_F = s([p(u),p(v)]_L).
The R-linear section s : L → F preserves brackets and therefore
defines an R-Lie homomorphism L → F. -/
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

/-- For an R-Lie algebra L projective as an R-module, with
free cover F and bracket [u,v]_F = s([p(u),p(v)]_L), the
canonical R-linear projection p : F → L preserves brackets.
It is a left inverse to the projective Lie inclusion s. -/
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

/-- For a commutative ring R and an R-Lie algebra L projective
as an R-module, let p : F → L be its free-cover Lie projection.
If p(u) = 0, then [u,v]_F = 0 for every v ∈ F. Thus ker(p)
is a central Lie ideal of the free-module cover. -/
theorem projectiveFreeCover_lie_eq_zero_of_projection_eq_zero
    (x y : ProjectiveFreeCover R L) (hx : projectiveCoverProjection R L x = 0) :
    ⁅x, y⁆ = 0 := by
  rw [projectiveFreeCover_lie]
  have hx' : projectiveCoverLinearProjection R L x = 0 := hx
  rw [hx', zero_lie, map_zero]

/-- For a commutative ring R and an R-Lie algebra L, the
underlying free-cover module F = L →₀ R has basis indexed by L,
with vector δ_x the function equal to 1 at x and zero elsewhere.
The index type L may have arbitrary cardinality. -/
def projectiveFreeCoverBasis : Module.Basis L R (ProjectiveFreeCover R L) :=
  Finsupp.basisSingleOne

end LieAlgebra
