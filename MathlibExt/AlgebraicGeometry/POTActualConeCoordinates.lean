/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.POTAffineModuleFrames

/-!
# The actual global cone embedding in POT coordinates

Every actual cone-image point is transported by its native scheme/point
arrow to the fixed coefficient point. Its obstruction vector and every
tangent translation are then exactly the native affine POT cone functor.
The module frames commute with all coefficient maps. This binds the
global closed conical embedding to the actual cotangent presentation,
including nonreduced test algebras and all coefficient arrows.
Source: Behrend--Fantechi, arXiv:alg-geom/9601010, Section4;
Manolache, arXiv:0805.2065v2, Condition3.3/Construction3.6.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 800000
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.POTActualConeCoordinates

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.AlgebraicGeometry
open StackCycleGeometry StackAffineModules StackFibreModels StackBundleCones AffineConeAtlas

variable {S : Scheme.{0}} {X Y : Stack S} {f : StackHom X Y}
  (C : IntrinsicConeModel f) (E : VectorBundleStack X) (i : ConeEmbedding C E)
  (c : IntrinsicConeChart f)
  (P : letI := c.geometry.algebra; ConePresentation c.presentation)
  (B : POTAffineModuleFrames.Coefficients c.geometry.source.U c.geometry.sourcePoint)
  (F : letI := c.geometry.algebra;
    POTAffineModuleFrames.Frame E c.geometry.source.U c.geometry.sourcePoint c.presentation P B)

structure Model where
  transport : letI := c.geometry.algebra;
    ∀ (R : CommAlgCat.{0} Γ(c.geometry.source.U.left, ⊤)) (a : IntrinsicConePoint c.presentation R),
      let q := coneObject c.presentation (C.views c).diagram R a
      NativePointTransport ((actualConeImage C E i.map c).obj q).base (B.functor.obj (op R)) (.of R)
        (actualConeScheme C E i.map c q)
        (POTAffineModuleFrames.schemeIso c.geometry.source.U c.geometry.sourcePoint B R)
        (actualConeToPoint C E i.map i.conical.sourceProjection c q)
        (POTAffineModuleFrames.pointArrow c.geometry.source.U c.geometry.sourcePoint B R)
  values : letI := c.geometry.algebra;
    ∀ (R : CommAlgCat.{0} Γ(c.geometry.source.U.left, ⊤)) (a : IntrinsicConePoint c.presentation R),
      (F.one R).hom
        ((E.linear.diagram.restriction (transport R a).iso.inv).degreeOne
          (E.linear.diagram.pointValue ((actualConeImage C E i.map c).obj
            (coneObject c.presentation (C.views c).diagram R a)))) =
      ((POTConeFunctorModels.coneFunctor c.presentation P R).obj a).value
  arrows : letI := c.geometry.algebra;
    ∀ (R T : CommAlgCat.{0} Γ(c.geometry.source.U.left, ⊤))
      (a : IntrinsicConePoint c.presentation R) (b : IntrinsicConePoint c.presentation T)
      (h : coneObject c.presentation (C.views c).diagram T b ⟶
        coneObject c.presentation (C.views c).diagram R a) (j : Fin P.zeroRank),
      (F.zero T).hom
        ((E.linear.diagram.restriction (transport T b).iso.inv).degreeZero
          (E.linear.diagram.arrowTranslation ((actualConeImage C E i.map c).map h))) j =
      coneArrowTangent c.presentation (C.views c).diagram h (P.zeroMap (Pi.single j 1))

end MathlibExt.AlgebraicGeometry.POTActualConeCoordinates
