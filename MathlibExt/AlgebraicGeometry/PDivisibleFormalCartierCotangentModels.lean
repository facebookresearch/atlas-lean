/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.PDivisibleCartierTowerModels
public import MathlibExt.AlgebraicGeometry.PDivisibleFiniteTangentModels

/-!
# Finite Cartier cotangents mapped from the actual formal Lie cotangent

The finite module is the genuine augmentation ideal modulo its square
of the original finite dual. Its representation sends each ideal class
to the literal second coordinate of the original group point, on every
p-nilpotent algebra and square-zero module. Projection from the formal
cotangent is fixed by the original finite tangent inclusion on that
entire test category, and all finite transitions are the original
dualized group divisions. These are the finite-to-formal maps used in
integral Hodge--Tate realization.

Sources: Messing, The crystals associated to Barsotti--Tate groups,
Chapter II; Scholze--Weinstein, arXiv:1211.6357v2, Sections 1--3.
Construction of this geometric comparison remains separate Wanted work.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.PDivisibleFormalCartierCotangentModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open PDivisibleGroupSchemes PDivisibleCartierTowerModels PDivisibleTangentTests
open PDivisibleLieModels
open FiniteCartierCharacterModels GroupZeroCotangentModels
open scoped _root_.CategoryTheory.MonObj

variable (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
  (G : PDivisibleGroup (Spec (.of R)) p) (D : CartierDualTower p R G)
  (L : LieModel p R D.group)

/-- The original square-zero group point underlying a genuine finite tangent vector. -/
def finiteTangentPoint (n : ℕ) (T : Test p R)
    (z : (PDivisibleFiniteTangentModels.tangent p R D.group n).obj T) :
    extensionScheme p R T ⟶ D.group.levels.obj n :=
  Additive.toMul
    (((kernel.ι (PDivisibleFiniteTangentModels.evaluation p R D.group n)).app T).hom z)

/-- Recover the full original finite-dual coefficient map on this nilpotent point. -/
def tangentCoordinates (n : ℕ) (T : Test p R)
    (z : (PDivisibleFiniteTangentModels.tangent p R D.group n).obj T) :
    (dualAugmentedAlgebra R (Coordinate R (finiteLevel p R G n))).ring →ₐ[R]
      Extension p R T :=
  ((coordinatePointAt R (dualLevel p R G n) (Extension p R T)
    (finiteTangentPoint p R G D n T z ≫ (finiteForget R).map (D.finiteIso n).hom)).ofConv).comp
      (MathlibExt.FiniteLocallyFreeBicommutativeHopfAlgCat.toBialgHom
        (dualCoordinateIso R (finiteLevel p R G n)).inv).toAlgHom

/-- The finite-to-formal comparison, normalized on the original tangent maps. -/
structure CotangentBridge where
  finite : ∀ n : ℕ,
    cotangentFunctor p R (ModuleCat.of R (DualFiniteCotangent p R G n)) ≅
      PDivisibleFiniteTangentModels.tangent p R D.group n
  finite_origin : ∀ (n : ℕ) (T : Test p R)
      (f : DualFiniteCotangent p R G n →ₗ[R] T.module)
      (a : (dualAugmentedAlgebra R (Coordinate R (finiteLevel p R G n))).ideal R),
    (tangentCoordinates p R G D n T ((finite n).hom.app T (ModuleCat.ofHom f)) a.val).snd =
      f (((dualAugmentedAlgebra R (Coordinate R (finiteLevel p R G n))).ideal R).toCotangent a)
  projection : ∀ n : ℕ, L.cotangent →ₗ[R] DualFiniteCotangent p R G n
  tangent_normalization : ∀ (n : ℕ) (T : Test p R)
      (f : DualFiniteCotangent p R G n →ₗ[R] T.module),
    (L.representation.hom.app T).hom (ModuleCat.ofHom (f.comp (projection n))) =
      (PDivisibleFiniteTangentModels.tangentInclusion p R D.group n).app T
        ((finite n).hom.app T (ModuleCat.ofHom f))
  transitions : ∀ (n m : ℕ) (h : n ≤ m),
    (finiteCotangentTransition p R G n m h).comp (projection m) = projection n

end MathlibExt.AlgebraicGeometry.PDivisibleFormalCartierCotangentModels
