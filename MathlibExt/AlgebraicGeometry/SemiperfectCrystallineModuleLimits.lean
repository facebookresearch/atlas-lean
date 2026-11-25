/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.SemiperfectCrystallinePDStages
public import MathlibExt.AlgebraicGeometry.FullPDCrystallineExtModules
public import MathlibExt.AlgebraicGeometry.PDivisibleCartierTowerModels
public import MathlibExt.AlgebraicGeometry.PDivisibleCartierGroupMaps
public import MathlibExt.CategoryTheory.ConstantModuleLimits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward

/-!
# Literal A_cris and B_cris⁺ evaluation of the fixed geometric Ext module

The integral module is the native inverse limit of the actual full-basis
Ext modules at A_cris/(p^(n+1)). The transition maps are precisely the
original crystalline restrictions and the coefficients are the literal
p-power projections of A_cris. The rational module is its actual scalar
extension to A_cris[1/p]. No independent module carrier is an input.

Finite projectivity and every PD-test comparison remain separate
construction/proof outputs. There is no completion along the PD ideal.

Source: Scholze--Weinstein1211.6357v2, Section3.2 and Proposition4.1.3.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.SemiperfectCrystallineModuleLimits

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open MathlibExt.RingTheory.SemiperfectWittPDEnvelopes
open MathlibExt.RingTheory.SemiperfectCrystallinePeriodRings
open MathlibExt.RingTheory.SemiperfectCrystallineResidues
open SemiperfectCrystallinePDStages PDivisibleGroupSchemes PDivisibleCartierTowerModels

variable (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [CharP R p]
  (A : UniversalEnvelope p R) (E : ResidueIdentification A) (P : PDStages p R A E)

/-- The only lift of A_cris coefficients is the required universe lift. -/
def liftCoefficients : Acris p R A →+* ULift.{1} (Acris p R A) where
  toFun := ULift.up
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The constant original A_cris ring over the actual finite test tower. -/
def constantCoefficients : ℕᵒᵖ ⥤ RingCat.{1} :=
  (Functor.const ℕᵒᵖ).obj (RingCat.of (ULift.{1} (Acris p R A)))

/-- Each coefficient map is the original literal p-power projection. -/
def finiteCoefficients : constantCoefficients p R A ⟶
    (finiteTests p R A E P).op ⋙
      (FullPDCrystallineSheaves.structureRingPresheaf p (hullPDBase p R A)
        (baseScheme p R A E) ⋙ forget₂ CommRingCat.{1} RingCat.{1}) where
  app n := RingCat.ofHom (finiteQuotient p R A n.unop).ulift
  naturality {n m} f := by
    apply RingCat.hom_ext
    apply RingHom.ext
    intro x
    rfl

variable (G : PDivisibleGroup (Spec (.of R)) p) (D : CartierDualTower p R G)

/-- The actual dual group, local Ext and target-multiplication module on the full basis. -/
def fullNativeModule :=
  FullPDCrystallineExtModules.nativeModule p (hullPDBase p R A) (baseScheme p R A E)
    (FullPDCrystallineSheaves.groupSheaf p (hullPDBase p R A) (baseScheme p R A E)
      D.group) 1

/-- Restrict the fixed full Ext module along exactly the original finite PD objects. -/
def finiteModules : PresheafOfModules.{1} (constantCoefficients p R A) :=
  (PresheafOfModules.pushforward (finiteCoefficients p R A E P)).obj
    (fullNativeModule p R A E G D)

/-- The actual A_cris-linear finite module diagram. -/
def finiteDiagram : ℕᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} (Acris p R A)) :=
  MathlibExt.CategoryTheory.ConstantModuleLimits.diagram
    (ULift.{1} (Acris p R A)) (finiteModules p R A E P G D)

/-- Integral evaluation is the native module limit of the original p-power restrictions. -/
def integralModule : ModuleCat.{1} (Acris p R A) :=
  (ModuleCat.restrictScalars (liftCoefficients p R A)).obj
    (limit (finiteDiagram p R A E P G D))

/-- Rational evaluation is exactly extension to the literal B_cris⁺ = A_cris[1/p]. -/
def rationalModule : ModuleCat.{1} (BcrisPlus p R A) :=
  (ModuleCat.extendScalars (algebraMap (Acris p R A) (BcrisPlus p R A))).obj
    (integralModule p R A E P G D)

/-- The actual finite integral value with its original A_cris coefficient map. -/
def finiteIntegralModule (n : ℕ) : ModuleCat.{1} (Acris p R A) :=
  (ModuleCat.restrictScalars (liftCoefficients p R A)).obj
    ((finiteDiagram p R A E P G D).obj (op n))

/-- Evaluation at every finite original thickening is the native limit projection. -/
def finiteProjection (n : ℕ) : integralModule p R A E P G D ⟶
    finiteIntegralModule p R A E P G D n :=
  (ModuleCat.restrictScalars (liftCoefficients p R A)).map
    (limit.π (finiteDiagram p R A E P G D) (op n))

/-- The finite value retains its original full-PD coefficient-ring action. -/
instance finiteNativeModule (n : ℕ) :
    Module (ULift.{1} (FiniteRing p R A n)) (finiteIntegralModule p R A E P G D n) :=
  ((fullNativeModule p R A E G D).obj (op (finiteTest p R A E P n))).isModule

/-- Its scalar action is the original quotient map to A_cris/(p^(n+1)). -/
theorem finite_projection_smul (n : ℕ) (r : Acris p R A)
    (x : integralModule p R A E P G D) :
    finiteProjection p R A E P G D n (r • x) =
      (ULift.up (finiteQuotient p R A n r)) •
        finiteProjection p R A E P G D n x := by
  exact (finiteProjection p R A E P G D n).hom.map_smul r x

namespace Maps

variable {G H : PDivisibleGroup (Spec (.of R)) p}
  (DG : CartierDualTower p R G) (DH : CartierDualTower p R H)
  (f : PDivisibleGroupMaps.Hom p G H)
  (d : PDivisibleCartierGroupMaps.DualHom p R f DG DH)

/-- The full coefficient map is the actual original Cartier-dual Ext precomposition. -/
def fullMap : fullNativeModule p R A E G DG ⟶ fullNativeModule p R A E H DH :=
  PDivisibleCartierGroupMaps.covariantFullMap d (hullPDBase p R A)
    (baseScheme p R A E).hom

/-- Restrict that same original geometric coefficient map to every actual finite stage. -/
def finiteModulesMap : finiteModules p R A E P G DG ⟶ finiteModules p R A E P H DH :=
  (PresheafOfModules.pushforward (finiteCoefficients p R A E P)).map
    (fullMap p R A E DG DH f d)

/-- The actual linear finite diagram map. -/
def finiteDiagramMap : finiteDiagram p R A E P G DG ⟶ finiteDiagram p R A E P H DH :=
  MathlibExt.CategoryTheory.ConstantModuleLimits.diagramMap
    (ULift.{1} (Acris p R A)) (finiteModulesMap p R A E P DG DH f d)

/-- The integral group map is the native inverse-limit map of those fixed finite maps. -/
def integralMap : integralModule p R A E P G DG ⟶ integralModule p R A E P H DH :=
  (ModuleCat.restrictScalars (liftCoefficients p R A)).map
    (lim.map (finiteDiagramMap p R A E P DG DH f d))

/-- The rational group map is literal B_cris⁺ scalar extension of the integral map. -/
def rationalMap : rationalModule p R A E P G DG ⟶ rationalModule p R A E P H DH :=
  (ModuleCat.extendScalars (algebraMap (Acris p R A) (BcrisPlus p R A))).map
    (integralMap p R A E P DG DH f d)

end Maps

end MathlibExt.AlgebraicGeometry.SemiperfectCrystallineModuleLimits
