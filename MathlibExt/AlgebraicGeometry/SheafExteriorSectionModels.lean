/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.LineBundleTaskContracts
public import MathlibExt.AlgebraicGeometry.GenericSectionMaps
public import MathlibExt.Algebra.Category.ModuleCat.PresheafExteriorPowers

/-!
# Actual sheaf exterior powers and local wedge generators

Exterior powers use the native sectionwise exterior algebra and
sheafification. Pullback comparison is fixed on every local wedge.
This is ordinary module-sheaf integration of the completed source
construction, not a new exterior-power existence theorem.

Source: AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b,
Algebra/Category/ModuleCat/Sheaf/SectionwiseAlgebras.lean, Apache 2.0;
Stacks Project, Tags 01CF and 01CR.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.SheafExteriorSectionModels

open CategoryTheory Opposite
open _root_.AlgebraicGeometry
open LineBundleTaskContracts CoherentCurveLinearSeries GenericSectionMaps

/-- The literal exterior presheaf followed by native sheafification. -/
def exteriorSheaf {T : Scheme.{0}} (M : T.Modules) (n : ℕ) : T.Modules :=
  (sheafifyModules T).obj (PresheafOfModules.extPow n ((forgetModules T).obj M))

/-- The actual sectionwise wedge and its sheafification image. -/
def wedgeSection {T : Scheme.{0}} (M : T.Modules) (n : ℕ) (W : T.Opens)
    (v : Fin n → Γ(M, W)) : Γ(exteriorSheaf M n,W) := by
  let F := (forgetModules T).obj M
  let P := PresheafOfModules.extPow n F
  let η := (PresheafOfModules.sheafificationAdjunction (𝟙 T.ringCatSheaf.obj)).unit.app P
  let e := (PresheafOfModules.extPowSections n F (op W)).symm
  exact (η.app (op W)).hom (e (exteriorPower.ιMulti Γ(T,W) n v))

/-- Native ordinary pullback/exterior comparison on every local generator. -/
structure PullbackExterior {T U : Scheme.{0}} (f : T ⟶ U) where
  comparison : ∀ (M : U.Modules) (n : ℕ),
    (Scheme.Modules.pullback f).obj (exteriorSheaf M n) ≅
      exteriorSheaf ((Scheme.Modules.pullback f).obj M) n
  normalized : ∀ (M : U.Modules) (n : ℕ) (V : U.Opens) (W : T.Opens)
    (h : W ≤ f ⁻¹ᵁ V) (v : Fin n → Γ(M,V)),
    (comparison M n).hom.app W
      (localPullbackSection f (exteriorSheaf M n) V W h (wedgeSection M n V v)) =
    wedgeSection ((Scheme.Modules.pullback f).obj M) n W
      (fun i => localPullbackSection f M V W h (v i))

end MathlibExt.AlgebraicGeometry.SheafExteriorSectionModels
