/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.OrdinaryOpenCutInclusions
public import MathlibExt.AlgebraicGeometry.IndSheafMonoidalModels
public import MathlibExt.AlgebraicGeometry.EnhancedIndQuotientModels
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.Analysis.Complex.Basic

/-!
# Actual closed half-line coefficients and their stable Ind colimit

The closed coefficient is the native cokernel of the original open cut
into the actual constant coefficient sheaf. The half-line diagram has
every transition fixed by the native quotient maps. Its Ind object is
the actual filtered colimit after the prescribed ordinary iota embedding.
The enhanced unit is its degree-zero object through the source quotient.
No independently selected stable object occurs.

Source: DK1311.2374v2 Sections4.6,4.7,4.9;
Mathlib56a005 native sheafification, cokernels, iota and colimits, Apache2.0.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.EnhancedStableCoefficientModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite TopologicalSpace
open CompactSupportIndSheaves IndSheafCoefficientModels IndSheafMonoidalModels
open OrdinarySheafOpenCuts OrdinaryOpenCutInclusions EnhancedIndQuotientModels

variable (X : TopCat.{0}) [HasSheafify (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)]

def openCutToPresheaf (F : OrdinarySheaf ℂ X) (U : Opens X) :
    cutPresheaf ℂ X F U ⟶ F.presheaf where
  app V := ModuleCat.ofHom (cutSections ℂ X F U V.unop).subtype
  naturality {V W} f := by ext s; rfl

def openCutToOriginal (F : OrdinarySheaf ℂ X) (U : Opens X) :
    (ordinaryOpenCut ℂ X U).obj F ⟶ F :=
  (presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)).map
    (openCutToPresheaf X F U) ≫
      (sheafificationAdjunction (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)).counit.app F

def closedCoefficient (U : Opens X) : OrdinarySheaf ℂ X :=
  cokernel (openCutToOriginal X (coefficientUnitSheaf ℂ X) U)

def closedCoefficientProjection (U : Opens X) : coefficientUnitSheaf ℂ X ⟶ closedCoefficient X U :=
  cokernel.π (openCutToOriginal X (coefficientUnitSheaf ℂ X) U)

variable (M : TopCat.{0})
  [HasSheafify (Opens.grothendieckTopology (enhancedSpace M).ambient) (ModuleCat.{0} ℂ)]

def realBelow (a : ℝ) : Opens (enhancedSpace M).ambient :=
  (⟨{p : M × EReal | p.2 < (a : EReal)},
    isOpen_Iio.preimage continuous_snd⟩ : Opens (M × EReal))

/-- Object comparisons and quotient-map transitions fix the entire original closed half-line diagram. -/
structure ClosedHalfLineDiagramSource where
  functor : ℝ ⥤ OrdinarySheaf ℂ (enhancedSpace M).ambient
  comparison : ∀ a : ℝ,
    closedCoefficient (enhancedSpace M).ambient (realBelow M a) ≅ functor.obj a
  transition : ∀ {a b : ℝ} (f : a ⟶ b),
    closedCoefficientProjection (enhancedSpace M).ambient (realBelow M a) ≫
      (comparison a).hom ≫ functor.map f =
        closedCoefficientProjection (enhancedSpace M).ambient (realBelow M b) ≫
          (comparison b).hom

variable (S : ClosedHalfLineDiagramSource M) (I : OrdinaryIndSource ℂ (enhancedSpace M).ambient)

def stableDiagram : ℝ ⥤ IndSheaf ℂ (enhancedSpace M).ambient :=
  S.functor ⋙ ordinaryToInd ℂ (enhancedSpace M).ambient I

structure StableColimitSource : Prop where
  [existsColimit : HasColimit (stableDiagram M S I)]

variable (C : StableColimitSource M S I)

def stableIndCoefficient : IndSheaf ℂ (enhancedSpace M).ambient :=
  letI := C.existsColimit
  colimit (stableDiagram M S I)

end MathlibExt.AlgebraicGeometry.EnhancedStableCoefficientModels
