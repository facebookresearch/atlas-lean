/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.PDCrystallineFrobeniusMaps
public import MathlibExt.CategoryTheory.RingedSliceExtModules
public import Mathlib.CategoryTheory.Sites.Pullback

/-!
# Source-normalized Cartier/Ext comparison for crystalline Frobenius

The slice functor is the native restriction along the actual PD
Frobenius reindexing. The source group comparison is fixed on every
original finite group point by the native scheme pullback projection.
The structure comparison fixes every original thickening-ring element.
Ext classes are transported by this exact native functor, with those
fixed source/target sheaf comparisons. The module comparison must agree
with that actual Ext map on every local-class sheafification unit and
with every full-PD restriction.

These normalized construction/proof outputs replace an unconstrained
Frobenius module isomorphism. The construction also applies to noninvertible Frobenius.

Source: BBM82; Scholze--Weinstein1211.6357v2, Sections3.1 and4.1.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CrystallineFrobeniusSourceComparison

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian
open _root_.AlgebraicGeometry Opposite
open MathlibExt.RingTheory.SemiperfectWittPDEnvelopes
open MathlibExt.RingTheory.SemiperfectCrystallinePeriodRings
open SemiperfectCrystallinePDStages SemiperfectCrystallineModuleLimits
open PDivisibleGroupSchemes PDivisibleCartierTowerModels PDivisibleCartierGroupMaps
open PDCrystallineFrobeniusMaps

variable (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [CharP R p]
  (A : UniversalEnvelope p R) (E : ResidueIdentification A) (P : PDStages p R A E)
  (F₀ : HullFrobenius (A := A)) (φ : CompletedFrobenius F₀)
  (C : Compatibility p R A E P F₀ φ)
  (G : PDivisibleGroup (Spec (.of R)) p) (D : CartierDualTower p R G)
  (Q : CartierFrobeniusVerschiebung p R G D)

abbrev Site := FullPDCrystallineTests.Obj p (hullPDBase p R A) (baseScheme p R A E)
abbrev siteTopology := FullPDCrystallineTests.topology p (hullPDBase p R A) (baseScheme p R A E)

/-- The actual original slice functor induced by PD Frobenius reindexing. -/
def sliceReindex (B : Site p R A E) : Over B ⥤
    Over (reindexedTest p R A E P F₀ φ C B) :=
  Over.post (reindex p R A E P F₀ φ C)

/-- The finite point comparison is the original native scheme pullback projection. -/
def finitePullbackPoint (B : Site p R A E) (n : ℕ)
    (x : (FullPDCrystallineTests.reductions p (hullPDBase p R A) (baseScheme p R A E)).obj B ⟶
      Q.dualTwist.group.levels.obj n) :
    (FullPDCrystallineTests.reductions p (hullPDBase p R A) (baseScheme p R A E)).obj
      (reindexedTest p R A E P F₀ φ C B) ⟶ D.group.levels.obj n := by
  let g := Q.dualTwistLevels.hom.app n
  refine Over.homMk (x.left ≫ g.left ≫
    pullback.fst (D.group.levels.obj n).hom (baseFrobenius p R)) ?_
  change (x.left ≫ g.left ≫ pullback.fst (D.group.levels.obj n).hom (baseFrobenius p R)) ≫
    (D.group.levels.obj n).hom = B.point ≫ baseFrobenius p R
  have hg : g.left ≫ pullback.snd (D.group.levels.obj n).hom (baseFrobenius p R) =
      (Q.dualTwist.group.levels.obj n).hom := g.w
  simp only [Category.assoc]
  rw [pullback.condition, ← Category.assoc g.left, hg, ← Category.assoc x.left, x.w]
  rfl

/-- An original finite scheme point enters the actual group sheaf by its native units. -/
def groupClassUnit (H : PDivisibleGroup (Spec (.of R)) p) (B : Site p R A E) (n : ℕ)
    (x : (FullPDCrystallineTests.reductions p (hullPDBase p R A) (baseScheme p R A E)).obj B ⟶
      H.levels.obj n) :
    (FullPDCrystallineSheaves.groupSheaf p (hullPDBase p R A) (baseScheme p R A E) H).obj.obj
      (op B) := by
  let x₀ := ((PDivisiblePointFunctors.levelInclusion (p := p) (S := Spec (.of R)) H n).app
    (op ((FullPDCrystallineTests.reductions p (hullPDBase p R A) (baseScheme p R A E)).obj B))).hom x
  let x₁ : (FullPDCrystallineSheaves.groupPresheaf p (hullPDBase p R A)
      (baseScheme p R A E) H).obj (op B) := ULift.up (Additive.ofMul x₀)
  exact (((sheafificationAdjunction (siteTopology p R A E) AddCommGrpCat.{1}).unit.app
    (FullPDCrystallineSheaves.groupPresheaf p (hullPDBase p R A) (baseScheme p R A E) H)).app
      (op B)) x₁

/-- Every original thickening-ring coefficient enters by the native ring-sheafification unit. -/
def structureClassUnit (B : Site p R A E) (r : ULift.{1} B.ring) :
    (FullPDCrystallineSheaves.structureSheaf p (hullPDBase p R A) (baseScheme p R A E)).obj.obj
      (op B) :=
  ((FullPDCrystallineExtModules.coefficientUnit p (hullPDBase p R A) (baseScheme p R A E)).app
    (op B)).hom r

section Slice

variable (B : Site p R A E)
  [h : (sliceReindex p R A E P F₀ φ C B).IsContinuous
    ((siteTopology p R A E).over B)
    ((siteTopology p R A E).over (reindexedTest p R A E P F₀ φ C B))]

/-- The functor transporting Ext is this exact native sheaf restriction. -/
def sliceRestriction :
    Sheaf ((siteTopology p R A E).over (reindexedTest p R A E P F₀ φ C B)) AddCommGrpCat.{1} ⥤
      Sheaf ((siteTopology p R A E).over B) AddCommGrpCat.{1} :=
  (sliceReindex p R A E P F₀ φ C B).sheafPushforwardContinuous AddCommGrpCat.{1}
    ((siteTopology p R A E).over B)
    ((siteTopology p R A E).over (reindexedTest p R A E P F₀ φ C B))

instance sliceRestriction_additive : (sliceRestriction p R A E P F₀ φ C B).Additive where
  map_add := by
    intro X Y f g
    apply Sheaf.hom_ext
    ext T x
    rfl

end Slice

/-- Fixed source and target sheaf comparisons, normalized on every original coefficient/point. -/
structure SliceComparison (B : Site p R A E) where
  [continuous : (sliceReindex p R A E P F₀ φ C B).IsContinuous
    ((siteTopology p R A E).over B)
    ((siteTopology p R A E).over (reindexedTest p R A E P F₀ φ C B))]
  [finiteLimits : PreservesFiniteLimits (sliceRestriction p R A E P F₀ φ C B)]
  [finiteColimits : PreservesFiniteColimits (sliceRestriction p R A E P F₀ φ C B)]
  structureIso : (sliceRestriction p R A E P F₀ φ C B).obj
      ((FullPDCrystallineSheaves.structureSheaf p (hullPDBase p R A) (baseScheme p R A E)).over
        (reindexedTest p R A E P F₀ φ C B)) ≅
    (FullPDCrystallineSheaves.structureSheaf p (hullPDBase p R A) (baseScheme p R A E)).over B
  groupIso : (sliceRestriction p R A E P F₀ φ C B).obj
      ((FullPDCrystallineSheaves.groupSheaf p (hullPDBase p R A) (baseScheme p R A E) D.group).over
        (reindexedTest p R A E P F₀ φ C B)) ≅
    (FullPDCrystallineSheaves.groupSheaf p (hullPDBase p R A) (baseScheme p R A E)
      Q.dualTwist.group).over B
  structureNormalization : ∀ (T : Over B) (r : ULift.{1} T.left.ring),
    (structureIso.hom.hom.app (op T))
      (structureClassUnit p R A E (reindexedTest p R A E P F₀ φ C T.left) r) =
        structureClassUnit p R A E T.left r
  finiteGroupNormalization : ∀ (T : Over B) (n : ℕ)
      (x : (FullPDCrystallineTests.reductions p (hullPDBase p R A) (baseScheme p R A E)).obj T.left ⟶
        Q.dualTwist.group.levels.obj n),
    (groupIso.hom.hom.app (op T))
      (groupClassUnit p R A E D.group (reindexedTest p R A E P F₀ φ C T.left) n
        (finitePullbackPoint p R A E P F₀ φ C G D Q T.left n x)) =
      groupClassUnit p R A E Q.dualTwist.group T.left n x

/-- Native exact-functor Ext transport with those actual source/target coefficient maps. -/
def localExtMap (B : Site p R A E) (N : SliceComparison p R A E P F₀ φ C G D Q B)
    (e : MathlibExt.CategoryTheory.RingedSliceExtModules.LocalExt (siteTopology p R A E)
      (FullPDCrystallineSheaves.structureRingSheaf p (hullPDBase p R A) (baseScheme p R A E))
      (FullPDCrystallineSheaves.groupSheaf p (hullPDBase p R A) (baseScheme p R A E) D.group)
      (reindexedTest p R A E P F₀ φ C B) 1) :
    MathlibExt.CategoryTheory.RingedSliceExtModules.LocalExt (siteTopology p R A E)
      (FullPDCrystallineSheaves.structureRingSheaf p (hullPDBase p R A) (baseScheme p R A E))
      (FullPDCrystallineSheaves.groupSheaf p (hullPDBase p R A) (baseScheme p R A E)
        Q.dualTwist.group) B 1 := by
  letI := N.continuous
  letI := N.finiteLimits
  letI := N.finiteColimits
  exact (Ext.mk₀ N.groupIso.inv).comp
    ((e.mapExactFunctor (sliceRestriction p R A E P F₀ φ C B)).comp
      (Ext.mk₀ N.structureIso.hom) (Nat.add_zero 1)) (Nat.zero_add 1)

/-- Reindex the fixed original full module through actual identity coefficient maps. -/
def reindexedModule :=
  (PresheafOfModules.pushforward (coefficientReindex p R A E P F₀ φ C)).obj
    (fullNativeModule p R A E G D)

/-- The full module comparison is fixed on every local Ext class and every PD restriction. -/
structure SourceComparison where
  slices : ∀ B : Site p R A E, SliceComparison p R A E P F₀ φ C G D Q B
  moduleIso : reindexedModule p R A E P F₀ φ C G D ≅
    fullNativeModule p R A E Q.source.twist.group Q.dualTwist
  localClassNormalization : ∀ (B : Site p R A E)
      (e : MathlibExt.CategoryTheory.RingedSliceExtModules.LocalExt (siteTopology p R A E)
        (FullPDCrystallineSheaves.structureRingSheaf p (hullPDBase p R A) (baseScheme p R A E))
        (FullPDCrystallineSheaves.groupSheaf p (hullPDBase p R A) (baseScheme p R A E) D.group)
        (reindexedTest p R A E P F₀ φ C B) 1),
    (moduleIso.hom.app (op B))
      ((FullPDCrystallineExtModules.localClassUnit p (hullPDBase p R A) (baseScheme p R A E)
        (FullPDCrystallineSheaves.groupSheaf p (hullPDBase p R A) (baseScheme p R A E) D.group)
        1).app (op (reindexedTest p R A E P F₀ φ C B)) e) =
      (FullPDCrystallineExtModules.localClassUnit p (hullPDBase p R A) (baseScheme p R A E)
        (FullPDCrystallineSheaves.groupSheaf p (hullPDBase p R A) (baseScheme p R A E)
          Q.dualTwist.group) 1).app (op B)
        (localExtMap p R A E P F₀ φ C G D Q B (slices B) e)

end MathlibExt.AlgebraicGeometry.CrystallineFrobeniusSourceComparison
