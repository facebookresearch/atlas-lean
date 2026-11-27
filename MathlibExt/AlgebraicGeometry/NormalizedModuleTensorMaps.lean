/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.GenericSectionMaps

/-!
# Fixed ordinary tensor/pullback and projection-formula maps

Pure tensor sections use the actual presheaf tensor and sheafification unit.
Pullback-tensor comparisons are characterized on all such local sections.
The projection-formula morphism is computed as the native adjunction mate,
and its unit map is the actual sheafified unitor/counit.

Generic tensor/pullback/projection-formula proofs are completed native/public
source integration inputs, not new Wanted results or arbitrary operators.
Sources: Stacks Tags 01CY/01CR; AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b,
StacksFrontier/AlgebraicGeometry/Duality/AffineProjectionFormula.lean
and Modules/ProjectionFormula.lean (Apache 2.0); native module adjunctions.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.NormalizedModuleTensorMaps

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.Opposite
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open MathlibExt.AlgebraicGeometry.AlgebraicLineBundleFamilies
open MathlibExt.AlgebraicGeometry.LineBundleTaskContracts
open MathlibExt.AlgebraicGeometry.GenericSectionMaps
open scoped TensorProduct

/-- The actual sheafification image of a local pure tensor. -/
def pureTensorSection (X : Scheme.{0}) (M N : X.Modules) (U : X.Opens)
    (s : Γ(M,U)) (t : Γ(N,U)) : Γ(moduleTensor X M N,U) := by
  let P : ModulePresheaves X := (forgetModules X).obj M ⊗ (forgetModules X).obj N
  exact ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P).app
    (op U) (s ⊗ₜ[Γ(X,U)] t)

/-- Comparison isomorphisms $f^*(M \otimes N) \cong f^* M \otimes f^* N$ of tensor products of
module sheaves, for a morphism of schemes $f : Y \to X$ and every pair of $\mathcal{O}_X$-modules
$M$, $N$, compatible with pure tensors: for opens $U \subseteq X$ and $W \subseteq f^{-1}(U)$ and
sections $s$ of $M$ and $t$ of $N$ over $U$, the pullback of $s \otimes t$ to $W$ goes to the
tensor product of the pullbacks of $s$ and $t$ to $W$. -/
structure PullbackTensor {X Y : Scheme.{0}} (f : Y ⟶ X) where
  comparison : ∀ M N : X.Modules,
    (Scheme.Modules.pullback f).obj (moduleTensor X M N) ≅
      moduleTensor Y ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N)
  normalized : ∀ (M N : X.Modules) (U : X.Opens) (W : Y.Opens)
    (h : W ≤ f ⁻¹ᵁ U) (s : Γ(M,U)) (t : Γ(N,U)),
    ((comparison M N).hom.app W)
      (localPullbackSection f (moduleTensor X M N) U W h (pureTensorSection X M N U s t)) =
    pureTensorSection Y ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N)
      W (localPullbackSection f M U W h s) (localPullbackSection f N U W h t)

/-- Literal ordinary projection-formula mate of the normalized pullback tensor comparison. -/
def projectionFormulaMap {X Y : Scheme.{0}} (f : Y ⟶ X) (T : PullbackTensor f)
    (M : Y.Modules) (L : X.Modules) :
    moduleTensor X ((Scheme.Modules.pushforward f).obj M) L ⟶
      (Scheme.Modules.pushforward f).obj (moduleTensor Y M ((Scheme.Modules.pullback f).obj L)) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _)
    ((T.comparison ((Scheme.Modules.pushforward f).obj M) L).hom ≫
      tensorMap ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app M)
        (𝟙 ((Scheme.Modules.pullback f).obj L)))

/-- The actual left unit tensor map is the sheafified unitor followed by the adjunction counit. -/
def leftUnitMap (X : Scheme.{0}) (L : X.Modules) :
    moduleTensor X (structureModule X) L ⟶ L :=
  (sheafifyModules X).map (λ_ ((forgetModules X).obj L)).hom ≫
    (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit.app L

end MathlibExt.AlgebraicGeometry.NormalizedModuleTensorMaps
