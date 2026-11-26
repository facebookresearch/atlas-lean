/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CanonicalLogRootArrowModels
public import MathlibExt.AlgebraicGeometry.RepresentableStackFppfSites

/-!
# The actual root image of a Kummer-flat log object

The root of the source log scheme is viewed over the target through
its complete original Grothendieck family category. The arrow to the
target root stack is fixed by the native infinite arrow and the literal
base-change total view. Fppf representability is a separate conclusion
on the actual scheme test fibres of that very arrow.

Source: Talpo--Vistoli1410.1164v2, Proposition6.14 and Section6.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.LogRootSiteImageModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.StackCycleGeometry _root_.AlgebraicGeometry.StackFibreModels
open EtaleLogSchemes EtaleLogDiagrams DenominatorRootStacks FiniteRootTowers
open KatoChartCoefficientModels LogRootSourceModels CanonicalLogRootArrowModels
open RelativeStackImageModels InfiniteRootPreservationModels
open RepresentableStackFppfModels

variable [InverseImageTheory.{0}]
  (I : NativeDFImages.{0}) (D : RegularSectionComparisons)
  {X Y : LogScheme.{0}} (f : EtaleLogSchemes.Hom X Y)
  (RX : RootRealization X D I) (RY : RootRealization Y D I)
  [HasBaseChanges RY.infinite.stack] [∀ n : Exponent, HasBaseChanges (RY.finite n).stack]
  (F : FiniteArrow I D f RX RY) (A : InfiniteArrow I D f RX RY F)
  (V : ImageModel f.map RX.infinite.stack)

/-- The actual composed total-category functor into the target root families. -/
def originalTotalMap : Total V.stack ⥤ Total RY.infinite.stack :=
  V.comparison.functor ⋙ totalMap A.morphism ⋙
    RootEtaleRestrictions.totalView f.map RY.infinite.stack

/-- The native image arrow has precisely this entire original family functor. -/
structure ImageArrow where
  morphism : StackHom V.stack RY.infinite.stack
  comparison : totalMap morphism ≅ originalTotalMap I D f RX RY F A V
  base_identity : ∀ r : Total V.stack,
    HEq ((comparison.hom.app r).base.left)
      (𝟙 r.base.left)

/-- The site image uses that same source arrow, with actual fppf scheme fibres. -/
structure FppfImage (B : ImageArrow I D f RX RY F A V) : Prop where
  fppf : HasFppfFibres B.morphism

def siteChart (B : ImageArrow I D f RX RY F A V)
    (H : FppfImage I D f RX RY F A V B) : Chart RY.infinite.stack :=
  ⟨V.stack, B.morphism, H.fppf⟩

end MathlibExt.AlgebraicGeometry.LogRootSiteImageModels
