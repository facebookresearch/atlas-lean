/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.EnhancedConvolutionModels
public import MathlibExt.AlgebraicGeometry.IndSheafDerivedAlphaModels

/-!
# The ordinary sheaf-valued enhanced Hom

Hom^E is computed as alpha Rpi_* RIhom(L^E K, R^E L). The two
representatives are native adjoints of the prescribed enhanced quotient.
RIhom is the native right adjoint of the actual ambient Ind tensor.
The projection is the original proper compactified real projection, and
alpha is the prescribed compact-Yoneda localization.

Source: DK arXiv:1311.2374v2, Definition 4.5.13, Lemma 4.5.14;
native adjoints/localization: Mathlib56a005855ea17e0b0958f73ec801ae140b0a1679,
Apache 2.0. The reconstruction map and its isomorphism are separate outputs.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.EnhancedSheafHomModels

open _root_.CategoryTheory _root_.Opposite TopologicalSpace
open CompactSupportIndSheaves EnhancedIndQuotientModels BorderedIndDerivedModels
open BoundedIndOperationSources EnhancedConvolutionModels
open IndSheafAlphaBetaModels IndSheafDerivedAlphaModels
open MathlibExt.CategoryTheory.NativeParametrizedAdjoints

variable (k : Type) [Field k] (M : TopCat.{0}) [T2Space M]
  [CompactSheafSource k M]
  [CompactSheafSource k (enhancedSpace M).ambient]
  [CompactSheafSource k (boundarySpace (enhancedSpace M))]

local instance sheafHomIndPreadditive (X : TopCat.{0}) [CompactSheafSource k X] :
    Preadditive (IndSheaf k X) := Abelian.toPreadditive

attribute [local instance] HasDerivedCategory.standard

variable (B : ProperSource k (boundaryInclusion (enhancedSpace M)))
  (P : InverseSource k (baseProjection M))

/-- The condition that the quotient functor `enhancedSourceProjection` onto the enhanced category,
from the bounded derived category of ind-sheaves of $k$-vector spaces ($k$ a field) on the ambient
space $M \times [-\infty, +\infty]$ of the bordered space `enhancedSpace M` (with interior
$M \times \mathbb{R}$), has both a left adjoint and a right adjoint, for a Hausdorff space $M$, the
given abelian structures on ind-sheaves (`CompactSheafSource`) and the given data `B` and `P`. -/
structure EnhancedRepresentativeSource : Prop where
  left : (enhancedSourceProjection k M B P).IsRightAdjoint
  right : (enhancedSourceProjection k M B P).IsLeftAdjoint

/-- L^E is the native left adjoint of the prescribed quotient. -/
def leftRepresentative (R : EnhancedRepresentativeSource k M B P) :
    EnhancedCategory k M B P ⥤ BoundedIndDerived k (enhancedSpace M).ambient :=
  letI := R.left
  (enhancedSourceProjection k M B P).leftAdjoint

/-- R^E is the native right adjoint of that same quotient. -/
def rightRepresentative (R : EnhancedRepresentativeSource k M B P) :
    EnhancedCategory k M B P ⥤ BoundedIndDerived k (enhancedSpace M).ambient :=
  letI := R.right
  (enhancedSourceProjection k M B P).rightAdjoint

def leftQuotientAdjunction (R : EnhancedRepresentativeSource k M B P) :
    leftRepresentative k M B P R ⊣ enhancedSourceProjection k M B P :=
  letI := R.left
  Adjunction.ofIsRightAdjoint (enhancedSourceProjection k M B P)

def rightQuotientAdjunction (R : EnhancedRepresentativeSource k M B P) :
    enhancedSourceProjection k M B P ⊣ rightRepresentative k M B P R :=
  letI := R.right
  Adjunction.ofIsLeftAdjoint (enhancedSourceProjection k M B P)

variable
  [HasSheafify (Opens.grothendieckTopology (enhancedSpace M).ambient)
    (ModuleCat.{0} k)]
  (T : TensorSource k (enhancedSpace M).ambient)

/-- Closedness refers only to the prescribed actual ambient tensor. -/
structure AmbientIhomSource : Prop where
  closed : ∀ K : BoundedIndDerived k (enhancedSpace M).ambient,
    ((tensorFunctor k (enhancedSpace M).ambient T).obj K).IsLeftAdjoint

/-- The original ambient derived internal Hom with native contravariant mate maps. -/
def ambientIhom (H : AmbientIhomSource k M T) :
    (BoundedIndDerived k (enhancedSpace M).ambient)ᵒᵖ ⥤
      BoundedIndDerived k (enhancedSpace M).ambient ⥤
        BoundedIndDerived k (enhancedSpace M).ambient :=
  letI := H.closed
  rightAdjointBifunctor (tensorFunctor k (enhancedSpace M).ambient T)

variable (Pi : ProperSource k (baseProjection M))
  (A : AlphaSource k M) [(alpha k M A).Additive]
  (E : ExactAlphaSource k M A)

/-- The actual proper projection followed by native cochain alpha. -/
def projectionAlpha :
    BoundedIndDerived k (enhancedSpace M).ambient ⥤ OrdinaryDerived k M :=
  properFunctor k (baseProjection M) Pi ⋙ (IsBounded k M).ι ⋙ derivedAlpha k M A E

/-- Hom^E, including every original morphism in both variables. -/
def homE (R : EnhancedRepresentativeSource k M B P) (H : AmbientIhomSource k M T) :
    (EnhancedCategory k M B P)ᵒᵖ ⥤ EnhancedCategory k M B P ⥤ OrdinaryDerived k M :=
  (leftRepresentative k M B P R).op ⋙ ambientIhom k M T H ⋙
    (Functor.whiskeringLeft (EnhancedCategory k M B P)
      (BoundedIndDerived k (enhancedSpace M).ambient)
      (BoundedIndDerived k (enhancedSpace M).ambient)).obj
        (rightRepresentative k M B P R) ⋙
    (Functor.whiskeringRight (EnhancedCategory k M B P)
      (BoundedIndDerived k (enhancedSpace M).ambient) (OrdinaryDerived k M)).obj
        (projectionAlpha k M Pi A E)

end MathlibExt.AlgebraicGeometry.EnhancedSheafHomModels
