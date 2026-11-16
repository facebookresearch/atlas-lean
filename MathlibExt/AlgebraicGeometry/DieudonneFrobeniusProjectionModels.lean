/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.NormalizedDieudonneFrobenius
public import Mathlib.CategoryTheory.Limits.Preserves.Limits

/-!
# Native cartesian and finite-projection Frobenius normalizations

Finite tensor maps are the original crystalline cartesian
linearizations followed by the normalized Cartier/Ext comparison.
The limit comparison has the original finite projections as its
components. Full-basis crystal F/V maps use that same source module
comparison and the original group V/F maps, respectively.

Source: BBM82; Scholze--Weinstein1211.6357v2, Section4.1.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DieudonneFrobeniusProjectionModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open MathlibExt.RingTheory.SemiperfectWittPDEnvelopes
open MathlibExt.RingTheory.SemiperfectCrystallinePeriodRings
open SemiperfectCrystallinePDStages SemiperfectCrystallineModuleLimits
open PDivisibleGroupSchemes PDivisibleCartierTowerModels PDivisibleCartierGroupMaps
open PDCrystallineFrobeniusMaps CrystallineFrobeniusSourceComparison NormalizedDieudonneFrobenius

variable (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [CharP R p]
  (A : UniversalEnvelope p R) (E : ResidueIdentification A) (P : PDStages p R A E)
  (F₀ : HullFrobenius (A := A)) (φ : CompletedFrobenius F₀)
  (C : Compatibility p R A E P F₀ φ)
  (G : PDivisibleGroup (Spec (.of R)) p) (D : CartierDualTower p R G)
  (Q : CartierFrobeniusVerschiebung p R G D)
  (N : SourceComparison p R A E P F₀ φ C G D Q)

/-- The finite tensor comparison is the actual original PD-cartesian linearization. -/
def finiteCartesianComparison (n : ℕ) :
    (ModuleCat.extendScalars.{1, 1, 1}
      ((FullPDCrystallineSheaves.structureRingPresheaf p (hullPDBase p R A) (baseScheme p R A E)).map
        (PDCrystallineFrobeniusMaps.finiteArrow p R A E P F₀ φ C n).op).hom).obj
      ((fullNativeModule p R A E G D).obj (op (finiteTest p R A E P n))) ⟶
    (fullNativeModule p R A E Q.source.twist.group Q.dualTwist).obj
      (op (finiteTest p R A E P n)) :=
  FullPDCrystallineExtModules.linearization p (hullPDBase p R A) (baseScheme p R A E)
    (FullPDCrystallineSheaves.groupSheaf p (hullPDBase p R A) (baseScheme p R A E) D.group)
    1 (PDCrystallineFrobeniusMaps.finiteArrow p R A E P F₀ φ C n) ≫
      N.moduleIso.hom.app (op (finiteTest p R A E P n))

/-- Every lifted limit projection is the fixed original finite PD/Ext Frobenius map. -/
theorem liftedLimitMap_projection (n : ℕ) :
    liftedLimitMap p R A E P F₀ φ C G D Q N ≫
      (ModuleCat.restrictScalars.{1, 1, 1} (liftedFrobenius p R A F₀ φ)).map
        (limit.π (finiteDiagram p R A E P Q.source.twist.group Q.dualTwist) (op n)) =
      limit.π (finiteDiagram p R A E P G D) (op n) ≫
        finiteMap p R A E P F₀ φ C G D Q N n := by
  rw [liftedLimitMap, Category.assoc, preservesLimitIso_inv_π, limit.map_π]
  rfl

/-- The full crystal's covariant F is the original group-V map after native source reindexing. -/
def crystallineFrobenius : reindexedModule p R A E P F₀ φ C G D ⟶ fullNativeModule p R A E G D :=
  N.moduleIso.hom ≫
    Maps.fullMap p R A E Q.dualTwist D (verschiebungHom p R G Q.source) Q.dualVerschiebung

/-- The full crystal's covariant V is the original group-F map with the same source reindexing. -/
def crystallineVerschiebung : fullNativeModule p R A E G D ⟶ reindexedModule p R A E P F₀ φ C G D :=
  Maps.fullMap p R A E D Q.dualTwist (frobeniusHom p R G Q.source) Q.dualFrobenius ≫
    N.moduleIso.inv

/-- The full-basis p-products concern exactly those two actual crystal maps. -/
structure FullCrystalProducts : Prop where
  vf : crystallineVerschiebung p R A E P F₀ φ C G D Q N ≫
    crystallineFrobenius p R A E P F₀ φ C G D Q N = p • 𝟙 (fullNativeModule p R A E G D)
  fv : crystallineFrobenius p R A E P F₀ φ C G D Q N ≫
    crystallineVerschiebung p R A E P F₀ φ C G D Q N =
      p • 𝟙 (reindexedModule p R A E P F₀ φ C G D)

end MathlibExt.AlgebraicGeometry.DieudonneFrobeniusProjectionModels
