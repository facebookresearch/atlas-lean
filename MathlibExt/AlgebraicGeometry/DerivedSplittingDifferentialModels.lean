/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AffineSplittingCotangentActions

/-!
# Cotangent differentials from the actual splitting/deformation action

The deformation map is the literal native based-fibre pullback map of
the original prestack natural transformation, using the prescribed
endpoint/diagonal path comparison. The cotangent arrow is normalized
by its Hom precomposition on every actual square-zero kernel test.
The whole homotopy is natural under actual coefficient-module maps.

In the affine chart application the source represents algebra
splittings, and the target represents F(A plus M) over F(A). Thus the
normalization uses F applied to each splitting. It does not assert
f*L_F=L_A. Whole affine/parameter/gauge diagram assembly and its
generator-normalized de Rham comparison remain separate source work.

References: PTVV1111.3209v4, Section1.2; HAGII math/0404373v7,
Sections1.3.7/1.4.1, actual cotangent corepresentability.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DerivedSplittingDifferentialModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory _root_.Opposite
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open MathlibExt.AlgebraicGeometry.DerivedCotangentModels
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicGeometry.SimplicialDerivedModels
open MathlibExt.AlgebraicGeometry.SimplicialHomotopyLimits
open MathlibExt.AlgebraicGeometry.AffineSplittingCotangentActions
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open scoped Simplicial

universe u

variable {k : Type u} [CommRing k]

/-- A native path map preserves both actual endpoint maps and the diagonal origin. -/
structure SourcePathMap {X Y : SSet.{u + 1}} (f : X ⟶ Y) (P : KanPathModel X) (Q : KanPathModel Y) where
  map : P.P ⟶ Q.P
  endpoints : map ≫ prod.lift Q.p₀ Q.p₁ = prod.lift P.p₀ P.p₁ ≫ prod.map f f
  diagonal : P.ι ≫ map = f ≫ Q.ι

variable (X Y : DerivedPrestack.{u, u + 1} k) (f : X.functor ⟶ Y.functor)
  (A : SAlg k) (x : (Δ[0] : SSet.{u + 1}) ⟶ X.functor.obj A)
  (PX : KanPathModel (X.functor.obj A)) (PY : KanPathModel (Y.functor.obj A))
  (P : SourcePathMap (f.app A) PX PY)

/-- The native full deformation map uses the same actual functorial projection square and path endpoints. -/
def deformationAlongMap (E : SquareZeroExtension A) :
    deformationFibre X E x PX ⟶ deformationFibre Y E (x ≫ f.app A) PY :=
  pullback.map (prod.map (X.functor.map E.projection) x) (prod.lift PX.p₀ PX.p₁)
    (prod.map (Y.functor.map E.projection) (x ≫ f.app A)) (prod.lift PY.p₀ PY.p₁)
    (prod.map (f.app E.algebra) (𝟙 (Δ[0] : SSet.{u + 1}))) P.map
    (prod.map (f.app A) (f.app A))
    (by
      apply prod.hom_ext <;> simp [f.naturality])
    P.endpoints.symm

/-- The original cotangent Hom precomposition, retaining its actual closed module map in every degree. -/
def moduleHomPrecompose {N : ShuffleAlgebraFunctor k} {L L' V : RightModule k (coefficientCategory N A)}
    (d : L ⟶ L') : moduleHomSpace L' V ⟶ moduleHomSpace L V :=
  let z := (DGFunctor.homEquivDGCycles k L L') d
  (liftSimplicial.{u}).map ((cochainToSSet k).map
    (eHomWhiskerRight (Cochains k) (dgClosedHomOf (C := RightModule k (coefficientCategory N A))
      k z.val z.property) (ForgetEnrichment.of _ V)))

variable {N : ShuffleAlgebraFunctor k}
  (CX : CotangentRepresentation N X A x PX)
  (CY : CotangentRepresentation N Y A (x ≫ f.app A) PY)

/-- The differential is fixed by the actual splitting map on the whole square-zero coefficient functor. -/
structure CotangentPointDifferential where
  map : CY.module.obj ⟶ CX.module.obj
  homotopy : ∀ (E : SplitExtension A) (V : KernelModuleModel N E),
    moduleHomSpace CX.module.obj V.module ⊗ (Δ[1] : SSet.{u + 1}) ⟶
      deformationFibre Y E.toSquareZeroExtension (x ≫ f.app A) PY
  source : ∀ (E : SplitExtension A) (V : KernelModuleModel N E),
    parameterAt _ 0 ≫ homotopy E V =
      CX.map E V ≫ deformationAlongMap X Y f A x PX PY P E.toSquareZeroExtension
  target : ∀ (E : SplitExtension A) (V : KernelModuleModel N E),
    parameterAt _ 1 ≫ homotopy E V = moduleHomPrecompose A map ≫ CY.map E V
  natural : ∀ {E E' : SplitExtension A} (V : KernelModuleModel N E)
    (V' : KernelModuleModel N E') (a : KernelMorphism V V'),
    (moduleHomMap CX.module.obj a.module ⊗ₘ 𝟙 (Δ[1] : SSet.{u + 1})) ≫ homotopy E' V' =
      homotopy E V ≫ deformationMap Y a.algebra a.projection (x ≫ f.app A) PY

end MathlibExt.AlgebraicGeometry.DerivedSplittingDifferentialModels
