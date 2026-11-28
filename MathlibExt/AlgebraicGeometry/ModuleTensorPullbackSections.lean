/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.GeometricHiggsFamilies
public import MathlibExt.AlgebraicGeometry.Modules.SectionPullback

/-!
# Local-section normalization for the fixed module tensor pullback

Local pullbacks are computed from the native pullback/pushforward adjunction
unit and actual restriction maps. A tensor comparison is an isomorphism
between these fixed native operations, characterized on every local pure
tensor, not an arbitrary tensor or pullback operation.

The canonical producer is source-complete in AxiomMath/Stacks,
c496df0d9beea9deaeabcea8492605f9a0a2313b,
StacksFrontier/Topology/Sheaves/RingedSpace/ModulePullbackTensor.lean
and AlgebraicGeometry/Modules/ZariskiRingedToposPullbackTensor.lean
(Apache 2.0). Its source-to-native integration datum is explicit here;
no duplicate Wanted existence theorem for that ordinary producer is added.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.ModuleTensorPullbackSections
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.Opposite
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open MathlibExt.AlgebraicGeometry.AlgebraicLineBundleFamilies
open MathlibExt.AlgebraicGeometry.LineBundleTaskContracts
open MathlibExt.AlgebraicGeometry.GeometricHiggsFamilies

universe u

/-- Further restriction to an actual source open contained in the preimage. -/
def localPullbackOn {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Y.Modules)
    (U : Y.Opens) (V : X.Opens) (h : V ≤ f ⁻¹ᵁ U) (s : Γ(L,U)) :
    Γ((Scheme.Modules.pullback f).obj L,V) :=
  ((Scheme.Modules.pullback f).obj L).presheaf.map (homOfLE h).op
    (localPullback f L U s)

/-- A fully locally normalized comparison of the fixed native operations. -/
structure PullbackTensorData {X Y : Scheme.{u}} (f : X ⟶ Y) where
  comparison : ∀ (L M : Y.Modules),
    (Scheme.Modules.pullback f).obj (moduleTensor Y L M) ≅
      moduleTensor X ((Scheme.Modules.pullback f).obj L) ((Scheme.Modules.pullback f).obj M)
  naturality : ∀ {L L' M M' : Y.Modules} (a : L ⟶ L') (b : M ⟶ M'),
    (Scheme.Modules.pullback f).map (tensorMap a b) ≫ (comparison L' M').hom =
      (comparison L M).hom ≫ tensorMap ((Scheme.Modules.pullback f).map a)
        ((Scheme.Modules.pullback f).map b)
  local_normalization : ∀ (L M : Y.Modules) (U : Y.Opens) (V : X.Opens)
    (h : V ≤ f ⁻¹ᵁ U) (s : Γ(L,U)) (t : Γ(M,U)),
    ((comparison L M).hom.val.app (op V)).hom
      (localPullbackOn f (moduleTensor Y L M) U V h (localTensor L M U s t)) =
    localTensor ((Scheme.Modules.pullback f).obj L) ((Scheme.Modules.pullback f).obj M) V
      (localPullbackOn f L U V h s) (localPullbackOn f M U V h t)

end MathlibExt.AlgebraicGeometry.ModuleTensorPullbackSections
