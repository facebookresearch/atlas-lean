/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Homotopy.HSpaceCommonUnitFibration
public import MathlibExt.AlgebraicTopology.SimplicialSet.SimplexRelativeTotal
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetModelStructure
public import Mathlib.CategoryTheory.MorphismProperty.Factorization

/-!
# The actual relative common-base total for the original H-space map

The selected simplicial model structure factors the actual common-base map
as a cofibration followed by a trivial fibration. Every intermediate
carrier, projection and map is computed from this factorization and the
original map. The entire original singular-map square is retained.

Ordinary integral homology of the arbitrary original continuous map first
gives the common-total homology isomorphism. The actual trivial-fibration
comparison then gives the inclusion's homology isomorphism. Applying the
original simplex-resolution relative augmentation proves acyclicity of
the actual relative coefficient total.

No monomorphism, factorization model, cover-homology, relative-acyclicity,
or expected weak/homotopy-equivalence witness is an outer premise. The
relative fiber/coinvariants induction is still needed for cover homology.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite
open scoped Simplicial SSet.modelCategoryQuillen

universe u

public section

namespace TopCat.HSpaceCommonUnitFibration

/-- The selected factorization of the actual original common-base map. -/
def commonRelativeFactorization {X Y : TopCat.{u}} (f : X ⟶ Y) :
    MorphismProperty.MapFactorizationData
      (cofibrations SSet.{u}) (trivialFibrations SSet.{u}) (commonTotalMap f) :=
  MorphismProperty.factorizationData (cofibrations SSet.{u})
    (trivialFibrations SSet.{u}) (commonTotalMap f)

/-- The actual intermediate carrier chosen by the selected model structure. -/
abbrev relativeIntermediate {X Y : TopCat.{u}} (f : X ⟶ Y) : SSet.{u} :=
  (commonRelativeFactorization f).Z

/-- The actual original source inclusion into that intermediate carrier. -/
def relativeInclusion {X Y : TopCat.{u}} (f : X ⟶ Y) :
    unitTotal X ⟶ relativeIntermediate f := (commonRelativeFactorization f).i

/-- The actual trivial-fibration comparison to the original common target. -/
def relativeComparison {X Y : TopCat.{u}} (f : X ⟶ Y) :
    relativeIntermediate f ⟶ commonTarget f := (commonRelativeFactorization f).p

/-- The entire factorization recovers the original common-base map. -/
theorem relativeInclusion_comparison {X Y : TopCat.{u}} (f : X ⟶ Y) :
    relativeInclusion f ≫ relativeComparison f = commonTotalMap f :=
  (commonRelativeFactorization f).fac

/-- Monicity is derived from the actual selected cofibration. -/
theorem relativeInclusion_mono {X Y : TopCat.{u}} (f : X ⟶ Y) :
    Mono (relativeInclusion f) := by
  let d := commonRelativeFactorization f
  let i : unitTotal X ⟶ relativeIntermediate f := d.i
  have hi : cofibrations SSet.{u} i := d.hi
  have hm : Mono i :=
    (congrArg (fun P : MorphismProperty SSet.{u} => P i)
      SSet.modelCategoryQuillen.cofibrations_eq).mp hi
  exact hm

/-- Fibrancy is derived from the actual selected trivial fibration. -/
theorem relativeComparison_fibration {X Y : TopCat.{u}} (f : X ⟶ Y) :
    Fibration (relativeComparison f) := by
  let d := commonRelativeFactorization f
  let r : relativeIntermediate f ⟶ commonTarget f := d.p
  have hr : trivialFibrations SSet.{u} r := d.hp
  exact ((mem_trivialFibrations_iff r).mp hr).1

/-- Weak equivalence is derived from that same actual comparison. -/
theorem relativeComparison_mem_realizationWeakEquivalences
    {X Y : TopCat.{u}} (f : X ⟶ Y) :
    SSet.realizationWeakEquivalences (relativeComparison f) := by
  let d := commonRelativeFactorization f
  let r : relativeIntermediate f ⟶ commonTarget f := d.p
  have hr : trivialFibrations SSet.{u} r := d.hp
  have hw : WeakEquivalence r := ((mem_trivialFibrations_iff r).mp hr).2
  exact (weakEquivalence_iff r).mp hw

/-- The intermediate carrier projects to the original source nerve base. -/
def relativeProjection {X Y : TopCat.{u}} (f : X ⟶ Y) :
    relativeIntermediate f ⟶
      CategoryTheory.nerve (SSet.FundamentalGroupoid (TopCat.toSSet.obj X)) :=
  relativeComparison f ≫ pullback.fst (baseMap f) (unitProjection Y)

/-- The actual inclusion and projection retain the original source unit fibration. -/
theorem relativeInclusion_projection {X Y : TopCat.{u}} (f : X ⟶ Y) :
    relativeInclusion f ≫ relativeProjection f = unitProjection X :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ pullback.fst (baseMap f) (unitProjection Y))
      (relativeInclusion_comparison f)).trans (commonTotalMap_fst f))

/-- The computed intermediate projection is itself a fibration over the same base. -/
theorem relativeProjection_fibration {X Y : TopCat.{u}} (f : X ⟶ Y) :
    Fibration (relativeProjection f) := by
  let : Fibration (relativeComparison f) := relativeComparison_fibration f
  let : Fibration (unitProjection Y) := unitProjection_isFibration Y
  let : Fibration (pullback.fst (baseMap f) (unitProjection Y)) := inferInstance
  change Fibration (relativeComparison f ≫ pullback.fst (baseMap f) (unitProjection Y))
  infer_instance

/-- The internal factorization still returns the original singular map through the original
retracts. -/
theorem relativeInclusion_original {X Y : TopCat.{u}} (f : X ⟶ Y) :
    relativeInclusion f ≫
      (relativeComparison f ≫ commonTargetComparison f ≫ SSet.mappingPathRetract
        (SSet.KanComplex.nativeCoverUnit (TopCat.toSSet.obj Y))) =
      SSet.mappingPathRetract (SSet.KanComplex.nativeCoverUnit (TopCat.toSSet.obj X)) ≫
        TopCat.toSSet.map f := by
  exact (Category.assoc (relativeInclusion f) (relativeComparison f)
    (commonTargetComparison f ≫ SSet.mappingPathRetract
      (SSet.KanComplex.nativeCoverUnit (TopCat.toSSet.obj Y)))).symm.trans
      ((congrArg (fun k => k ≫
        (commonTargetComparison f ≫ SSet.mappingPathRetract
          (SSet.KanComplex.nativeCoverUnit (TopCat.toSSet.obj Y))))
        (relativeInclusion_comparison f)).trans (commonTotalMap_original f))

/-- The actual source inclusion's homology is derived from ordinary homology of the original map. -/
theorem relativeInclusion_integralHomology_isIso
    {X Y : TopCat.{u}} [HSpace X] [HSpace Y]
    [PathConnectedSpace X] [PathConnectedSpace Y] (f : X ⟶ Y)
    (h : ∀ n : ℕ, IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor n).map f))
    (n : ℕ) :
    IsIso (SSet.homologyMap (relativeInclusion f)
      (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u}) n) := by
  let R : AddCommGrpCat.{u} := AlgebraicTopology.singularIntegralCoefficients
  let C := (SSet.chainComplexFunctor AddCommGrpCat.{u}).obj R
  let ci := C.map (relativeInclusion f)
  let cr := C.map (relativeComparison f)
  let cm := C.map (commonTotalMap f)
  have hM : QuasiIso cm :=
    (_root_.quasiIso_iff _).mpr (fun k =>
      (_root_.quasiIsoAt_iff_isIso_homologyMap _ k).mpr
        (commonTotalMap_integralHomology_isIso f (h 1) k (h k)))
  have hWeak := relativeComparison_mem_realizationWeakEquivalences f
  let : QuasiIso cr := hWeak.quasiIso_chainComplexMap_addCommGrp R
  have hFac : ci ≫ cr = cm :=
    (C.map_comp _ _).symm.trans (congrArg C.map (relativeInclusion_comparison f))
  let : QuasiIso (ci ≫ cr) := hFac.symm ▸ hM
  have hI : QuasiIso ci := _root_.quasiIso_of_comp_right ci cr
  have hOriginal : QuasiIso (SSet.chainComplexMap (relativeInclusion f) R) := hI
  exact (_root_.quasiIsoAt_iff_isIso_homologyMap
    (SSet.chainComplexMap (relativeInclusion f) R) n).mp (hOriginal.quasiIsoAt n)

/-- The actual relative coefficient total computed from the original map. -/
abbrev originalRelativeCoefficientTotal {X Y : TopCat.{u}} (f : X ⟶ Y) :
    ChainComplex AddCommGrpCat.{u} ℕ :=
  SSet.simplexRelativeCoefficientTotal
    (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})
    (relativeInclusion f) (relativeInclusion_projection f)

/-- Ordinary integral Hiso of an arbitrary original continuous H-space map
makes its actual relative common-base coefficient total acyclic. -/
theorem originalRelativeCoefficientTotal_acyclic_of_integralHomology_isIso
    {X Y : TopCat.{u}} [HSpace X] [HSpace Y]
    [PathConnectedSpace X] [PathConnectedSpace Y] (f : X ⟶ Y)
    (h : ∀ n : ℕ, IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor n).map f)) :
    (originalRelativeCoefficientTotal f).Acyclic := by
  let : Mono (relativeInclusion f) := relativeInclusion_mono f
  exact SSet.simplexRelativeCoefficientTotal_acyclic_of_homology_isIso
    (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})
    (relativeInclusion f) (relativeInclusion_projection f)
    (relativeInclusion_integralHomology_isIso f h)

end TopCat.HSpaceCommonUnitFibration

namespace TopCat.HSpaceCommonUnitFibration

private theorem relativeProjection_eq_computation {X Y : TopCat.{u}} (f : X ⟶ Y) :
    relativeProjection f = relativeComparison f ≫ pullback.fst (baseMap f) (unitProjection Y) := by
  unfold relativeProjection
  rfl

/-- The intermediate projection is the SAME comparison followed by the original base projection. -/
theorem relativeProjection_eq {X Y : TopCat.{u}} (f : X ⟶ Y) :
    relativeProjection f = relativeComparison f ≫ pullback.fst (baseMap f) (unitProjection Y) :=
  relativeProjection_eq_computation f

end TopCat.HSpaceCommonUnitFibration
