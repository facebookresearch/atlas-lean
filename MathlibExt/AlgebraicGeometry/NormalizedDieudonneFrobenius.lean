/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CrystallineFrobeniusSourceComparison
public import MathlibExt.AlgebraicGeometry.RationalDieudonneOperators
public import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-!
# The fixed native Dieudonne Frobenius base-change map

Each finite map is the actual crystalline restriction along the native
PD Frobenius arrow, followed by the source-normalized Cartier/Ext map.
All p-power restriction squares commute. The integral comparison is
the native limit map and scalar-restriction limit comparison, followed
by the native tensor adjunction. Hence its map and every finite
projection are determined before its isomorphism property is requested.

Integral and rational F/V use the isomorphism of this exact constructed
map. An unrelated Frobenius module isomorphism cannot replace it.
Frobenius on the coefficient ring need not be invertible.

Source: BBM82; Scholze--Weinstein1211.6357v2, Section4.1.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.NormalizedDieudonneFrobenius

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open MathlibExt.RingTheory.SemiperfectWittPDEnvelopes
open MathlibExt.RingTheory.SemiperfectCrystallinePeriodRings
open MathlibExt.RingTheory.SemiperfectCrystallineResidues
open SemiperfectCrystallinePDStages SemiperfectCrystallineModuleLimits
open PDivisibleGroupSchemes PDivisibleCartierTowerModels PDivisibleCartierGroupMaps
open PDCrystallineFrobeniusMaps CrystallineFrobeniusSourceComparison

variable (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [CharP R p]
  (A : UniversalEnvelope p R) (E : ResidueIdentification A) (P : PDStages p R A E)
  (F₀ : HullFrobenius (A := A)) (φ : CompletedFrobenius F₀)
  (C : Compatibility p R A E P F₀ φ)
  (G : PDivisibleGroup (Spec (.of R)) p) (D : CartierDualTower p R G)
  (Q : CartierFrobeniusVerschiebung p R G D)
  (N : SourceComparison p R A E P F₀ φ C G D Q)

/-- The lifted coefficient map is exactly the original completed Frobenius. -/
abbrev liftedFrobenius : ULift.{1} (Acris p R A) →+* ULift.{1} (Acris p R A) := φ.hom.ulift

/-- The finite diagram retains its actual original full-PD coefficient action. -/
instance finiteDiagramNativeModule (n : ℕ) :
    Module (ULift.{1} (FiniteRing p R A n)) ((finiteDiagram p R A E P G D).obj (op n)) :=
  ((fullNativeModule p R A E G D).obj (op (finiteTest p R A E P n))).isModule

/-- The finite semilinear map is the actual PD-arrow restriction and normalized Ext map. -/
def finiteMap (n : ℕ) : (finiteDiagram p R A E P G D).obj (op n) ⟶
    (ModuleCat.restrictScalars (liftedFrobenius p R A F₀ φ)).obj
      ((finiteDiagram p R A E P Q.source.twist.group Q.dualTwist).obj (op n)) :=
  ModuleCat.ofHom
    (X := (finiteDiagram p R A E P G D).obj (op n))
    (Y := (ModuleCat.restrictScalars (liftedFrobenius p R A F₀ φ)).obj
      ((finiteDiagram p R A E P Q.source.twist.group Q.dualTwist).obj (op n))) {
    toFun x := (N.moduleIso.hom.app (op (finiteTest p R A E P n)))
      ((fullNativeModule p R A E G D).restrictₛₗ
        (PDCrystallineFrobeniusMaps.finiteArrow p R A E P F₀ φ C n).op x)
    map_add' x y := by simp only [map_add]
    map_smul' r x := by
      change (N.moduleIso.hom.app (op (finiteTest p R A E P n)))
        ((fullNativeModule p R A E G D).restrictₛₗ
          (PDCrystallineFrobeniusMaps.finiteArrow p R A E P F₀ φ C n).op
          (ULift.up (finiteQuotient p R A n r.down) • x)) =
        ULift.up (finiteQuotient p R A n (φ.hom r.down)) •
          (N.moduleIso.hom.app (op (finiteTest p R A E P n)))
            ((fullNativeModule p R A E G D).restrictₛₗ
              (PDCrystallineFrobeniusMaps.finiteArrow p R A E P F₀ φ C n).op x)
      rw [LinearMap.map_smulₛₗ, map_smul]
      congr 1 }

/-- Every finite projection uses the same native PD/restriction square. -/
def finiteDiagramMap : finiteDiagram p R A E P G D ⟶
    finiteDiagram p R A E P Q.source.twist.group Q.dualTwist ⋙
      ModuleCat.restrictScalars (liftedFrobenius p R A F₀ φ) where
  app n := finiteMap p R A E P F₀ φ C G D Q N n.unop
  naturality {m n} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    let u := SemiperfectCrystallinePDStages.finiteArrow p R A E P f.unop.le
    let aₘ := PDCrystallineFrobeniusMaps.finiteArrow p R A E P F₀ φ C m.unop
    let aₙ := PDCrystallineFrobeniusMaps.finiteArrow p R A E P F₀ φ C n.unop
    let M := fullNativeModule p R A E G D
    let H := fullNativeModule p R A E Q.source.twist.group Q.dualTwist
    have hi := congrArg (fun g => g (M.map aₘ.op x)) (N.moduleIso.hom.naturality u.op)
    change (N.moduleIso.hom.app (op (finiteTest p R A E P n.unop)))
      (M.map ((reindex p R A E P F₀ φ C).map u).op (M.map aₘ.op x)) =
      H.map u.op ((N.moduleIso.hom.app (op (finiteTest p R A E P m.unop)))
        (M.map aₘ.op x)) at hi
    have hc := congrArg (fun a => M.map a.op x)
      (finiteArrow_naturality p R A E P F₀ φ C f.unop.le)
    simp only [op_comp, PresheafOfModules.map_comp_apply] at hc
    change (N.moduleIso.hom.app (op (finiteTest p R A E P n.unop)))
      (M.map aₙ.op (M.map u.op x)) =
      H.map u.op ((N.moduleIso.hom.app (op (finiteTest p R A E P m.unop)))
        (M.map aₘ.op x))
    exact (congrArg (N.moduleIso.hom.app (op (finiteTest p R A E P n.unop))) hc.symm).trans hi

/-- Native scalar restriction is a right adjoint, so it preserves the actual module limits. -/
instance liftedRestriction_rightAdjoint :
    (ModuleCat.restrictScalars.{1, 1, 1} (liftedFrobenius p R A F₀ φ)).IsRightAdjoint :=
  (ModuleCat.extendRestrictScalarsAdj.{1, 1, 1} (liftedFrobenius p R A F₀ φ)).isRightAdjoint

/-- The lifted map is the native limit map with the native scalar-restriction limit isomorphism. -/
def liftedLimitMap : limit (finiteDiagram p R A E P G D) ⟶
    (ModuleCat.restrictScalars (liftedFrobenius p R A F₀ φ)).obj
      (limit (finiteDiagram p R A E P Q.source.twist.group Q.dualTwist)) :=
  lim.map (finiteDiagramMap p R A E P F₀ φ C G D Q N) ≫
    (preservesLimitIso (ModuleCat.restrictScalars (liftedFrobenius p R A F₀ φ))
      (finiteDiagram p R A E P Q.source.twist.group Q.dualTwist)).inv

/-- The integral semilinear map retains those exact underlying limit elements and coefficients. -/
def integralSemilinearMap : integralModule p R A E P G D ⟶
    (ModuleCat.restrictScalars φ.hom).obj
      (integralModule p R A E P Q.source.twist.group Q.dualTwist) :=
  ModuleCat.ofHom
    (X := integralModule p R A E P G D)
    (Y := (ModuleCat.restrictScalars φ.hom).obj
      (integralModule p R A E P Q.source.twist.group Q.dualTwist)) {
    toFun := liftedLimitMap p R A E P F₀ φ C G D Q N
    map_add' := (liftedLimitMap p R A E P F₀ φ C G D Q N).hom.map_add
    map_smul' r x := (liftedLimitMap p R A E P F₀ φ C G D Q N).hom.map_smul (ULift.up r) x }

/-- The actual Frobenius tensor comparison is the native adjunction mate of this fixed limit map. -/
def nativeComparison :
    (ModuleCat.extendScalars.{0, 0, 1} φ.hom).obj (integralModule p R A E P G D) ⟶
      integralModule p R A E P Q.source.twist.group Q.dualTwist :=
  ((ModuleCat.extendRestrictScalarsAdj.{1, 0, 0} φ.hom).homEquiv
    (integralModule p R A E P G D)
    (integralModule p R A E P Q.source.twist.group Q.dualTwist)).symm
      (integralSemilinearMap p R A E P F₀ φ C G D Q N)

/-- Isomorphism and p-products are requested for this exact map, with no independent base-change iso. -/
structure OperatorsNormalization where
  [comparisonIsIso : IsIso (nativeComparison p R A E P F₀ φ C G D Q N)]
  operators : SemiperfectDieudonneOperators.OperatorsRealization p R A E P G D Q F₀ φ
  baseChange_eq : operators.baseChange = asIso (nativeComparison p R A E P F₀ φ C G D Q N)

end MathlibExt.AlgebraicGeometry.NormalizedDieudonneFrobenius
