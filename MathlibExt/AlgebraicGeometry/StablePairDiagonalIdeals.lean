/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.StablePairJetComplexes
public import MathlibExt.AlgebraicGeometry.RationalResolution
public import MathlibExt.AlgebraicGeometry.LineBundleTaskContracts
public import MathlibExt.AlgebraicGeometry.AlgebraicDifferentialSheaves
public import Mathlib.Basic.Complex.Basic

/-!
# Actual ideal-square and diagonal modules for perfect-complex jets

The ideal is the actual kernel of the native structure-sheaf map of a
scheme immersion. Its square multiplication is fixed by the ordinary
tensor of the two kernel inclusions and the structure-sheaf product.
The conormal object is the actual cokernel of that multiplication,
pulled to the closed scheme.

The ambient diagonal ideal, its ordinary pullback to Y × Y, and its
quotient by its actual square are the modules of the
Huybrechts–Thomas source diagram (2.6), arXiv:0805.3527v2.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.StablePairDiagonalIdeals

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open _root_.AlgebraicGeometry
open CoherentCurveLinearSeries LineBundleTaskContracts AlgebraicLineBundleFamilies
open RationalResolution

/-- The actual multiplication of the structure module after sheafification. -/
def structureMultiplication (Z : Scheme) :
    moduleTensor Z (structureModule Z) (structureModule Z) ⟶ structureModule Z :=
  (sheafifyModules Z).map (λ_ ((forgetModules Z).obj (structureModule Z))).hom ≫
    (PresheafOfModules.sheafificationAdjunction (𝟙 Z.ringCatSheaf.obj)).counit.app
      (structureModule Z)

abbrev ideal {Y Z : Scheme} (i : Y ⟶ Z) : Z.Modules := kernel (structureUnit i)

def idealInclusion {Y Z : Scheme} (i : Y ⟶ Z) : ideal i ⟶ structureModule Z :=
  kernel.ι (structureUnit i)

/-- The actual source product of two local ideal sections. -/
def squareSource {Y Z : Scheme} (i : Y ⟶ Z) :
    moduleTensor Z (ideal i) (ideal i) ⟶ structureModule Z :=
  tensorMap (idealInclusion i) (idealInclusion i) ≫ structureMultiplication Z

/-- The ideal-valued multiplication is fixed by its native monomorphism into O_Z. -/
structure IdealSquare {Y Z : Scheme} (i : Y ⟶ Z) where
  map : moduleTensor Z (ideal i) (ideal i) ⟶ ideal i
  normalized : map ≫ idealInclusion i = squareSource i

def conormal {Y Z : Scheme} {i : Y ⟶ Z} (S : IdealSquare i) : Y.Modules :=
  (Scheme.Modules.pullback i).obj (cokernel S.map)

def diagonal (Y : Over (Spec (.of ℂ))) : Y.left ⟶ pullback Y.hom Y.hom :=
  pullback.lift (𝟙 _) (𝟙 _) rfl

def productEmbedding {Y Z : Over (Spec (.of ℂ))} (i : Y ⟶ Z) :
    pullback Y.hom Y.hom ⟶ pullback Z.hom Z.hom :=
  pullback.lift (pullback.fst Y.hom Y.hom ≫ i.left)
    (pullback.snd Y.hom Y.hom ≫ i.left) (by
      simp only [Category.assoc, Over.w i]
      exact pullback.condition)

/-- The literal ambient diagonal ideal restricted to the closed product. -/
def restrictedIdeal {Y Z : Over (Spec (.of ℂ))} (i : Y ⟶ Z) :
    (pullback Y.hom Y.hom).Modules :=
  (Scheme.Modules.pullback (productEmbedding i)).obj (ideal (diagonal Z))

def restrictedIdealMap {Y Z : Over (Spec (.of ℂ))} (i : Y ⟶ Z) :
    restrictedIdeal i ⟶ structureModule (pullback Y.hom Y.hom) :=
  (Scheme.Modules.pullback (productEmbedding i)).map (idealInclusion (diagonal Z)) ≫
    SheafOfModules.pullbackObjUnitToUnit (productEmbedding i).toRingCatSheafHom

def restrictedQuotient {Y Z : Over (Spec (.of ℂ))} (i : Y ⟶ Z)
    (S : IdealSquare (diagonal Z)) : (pullback Y.hom Y.hom).Modules :=
  (Scheme.Modules.pullback (productEmbedding i)).obj (cokernel S.map)

def quotientProjection {Y Z : Over (Spec (.of ℂ))} (i : Y ⟶ Z)
    (S : IdealSquare (diagonal Z)) : restrictedIdeal i ⟶ restrictedQuotient i S :=
  (Scheme.Modules.pullback (productEmbedding i)).map (cokernel.π S.map)

abbrev diagonalKernel {Y Z : Over (Spec (.of ℂ))} (i : Y ⟶ Z) :=
  kernel (restrictedIdealMap i)

end MathlibExt.AlgebraicGeometry.StablePairDiagonalIdeals
