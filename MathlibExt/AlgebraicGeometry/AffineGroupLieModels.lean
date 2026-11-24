/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CameralTorusBands
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.Algebra.Lie.BaseChange
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# The actual Lie algebra of an affine group scheme

The tangent space is the native derivation module at the actual identity
augmentation. Its bracket is fixed by commutators of actual invariant
derivations on the coordinate algebra. Invariance uses the coproduct
induced by the actual group multiplication, with both tensor generators
bound to the actual product projections.

This adapter supplies a finite Lie-algebra presentation, rather than
replacing the Lie algebra of the group by an unrelated finite carrier.
Source: Donagi--Gaitsgory arXiv:math/0005132v3, Section0.5; the affine
group/Lie-algebra construction via invariant derivations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.AffineGroupLieModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj _root_.AlgebraicGeometry
open scoped TensorProduct

variable {k : Type} [Field k]
  (G : Over (Spec (.of k))) [GrpObj G]
  (V : Type) [LieRing V] [LieAlgebra k V] [FiniteDimensional k V]

structure LieModel where
  coordinate : CommAlgCat.{0} k
  affine : Over.mk (Spec.algebraMap k coordinate) ≅ G
  augmentation : coordinate →ₐ[k] k
  identity : Spec.map (CommRingCat.ofHom augmentation.toRingHom) ≫
    affine.hom.left = η[G].left
  productChart : Spec (.of (coordinate ⊗[k] coordinate)) ≅ (G ⊗ G).left
  first : productChart.hom ≫ (fst G G).left =
    Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeft :
        coordinate →ₐ[k] coordinate ⊗[k] coordinate).toRingHom) ≫
      affine.hom.left
  second : productChart.hom ≫ (snd G G).left =
    Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight :
        coordinate →ₐ[k] coordinate ⊗[k] coordinate).toRingHom) ≫
      affine.hom.left
  coproduct : coordinate →ₐ[k] coordinate ⊗[k] coordinate
  multiplication : Spec.map (CommRingCat.ofHom coproduct.toRingHom) ≫
    affine.hom.left = productChart.hom ≫ μ[G].left
  invariant : V →ₗ[k] Derivation k coordinate coordinate
  tangent : letI : Algebra coordinate k := augmentation.toRingHom.toAlgebra
    V ≃ₗ[k] Derivation k coordinate k
  tangent_values : letI : Algebra coordinate k := augmentation.toRingHom.toAlgebra
    ∀ (v : V) (f : coordinate), tangent v f = augmentation (invariant v f)
  left_invariant : ∀ (v : V) (f : coordinate),
    coproduct (invariant v f) =
      TensorProduct.map (LinearMap.id : coordinate →ₗ[k] coordinate)
        (invariant v).toLinearMap (coproduct f)
  bracket : ∀ (v w : V) (f : coordinate),
    invariant ⁅v, w⁆ f = invariant v (invariant w f) - invariant w (invariant v f)

end MathlibExt.AlgebraicGeometry.AffineGroupLieModels
