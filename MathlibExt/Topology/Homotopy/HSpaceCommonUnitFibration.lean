/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Homotopy.HSpaceNerveBaseComparison
public import MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.NativeCoverCore
public import MathlibExt.AlgebraicTopology.SimplicialSet.GroupoidNerveKan
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanWeakFiniteSubarrow
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanWeakEquivalenceChains
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RightProper

/-!
# The original H-space map in common-base unit fibrations

Every map and comparison is computed from the original singular map and
its actual nerve-unit square. Integral H1 derives the base weak comparison.
Ordinary integral homology in degree n then derives homology isomorphism
of the actual common-base total map via its original retract square.
This does not assert the still-required relative-cover spectral comparison.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite
open scoped Simplicial SSet.modelCategoryQuillen

universe u

public section

namespace TopCat.HSpaceCommonUnitFibration

private abbrev base (X : TopCat.{u}) : SSet.{u} :=
  CategoryTheory.nerve (SSet.FundamentalGroupoid (TopCat.toSSet.obj X))

private abbrev unitMap (X : TopCat.{u}) : TopCat.toSSet.obj X ⟶ base X :=
  SSet.KanComplex.nativeCoverUnit (TopCat.toSSet.obj X)

/-- The fixed mapping-path total of the original nerve unit. -/
abbrev unitTotal (X : TopCat.{u}) : SSet.{u} :=
  SSet.mappingPathSpace (SSet.KanComplex.nativeCoverUnit (TopCat.toSSet.obj X))

/-- The actual derived fibration to the original groupoid-nerve base. -/
def unitProjection (X : TopCat.{u}) : unitTotal X ⟶
    CategoryTheory.nerve (SSet.FundamentalGroupoid (TopCat.toSSet.obj X)) :=
  SSet.mappingPathTarget (SSet.KanComplex.nativeCoverUnit (TopCat.toSSet.obj X))

/-- The actual original nerve base map. -/
def baseMap {X Y : TopCat.{u}} (f : X ⟶ Y) :
    CategoryTheory.nerve (SSet.FundamentalGroupoid (TopCat.toSSet.obj X)) ⟶
      CategoryTheory.nerve (SSet.FundamentalGroupoid (TopCat.toSSet.obj Y)) :=
  CategoryTheory.nerveMap (SSet.mapFundamentalGroupoid (TopCat.toSSet.map f))

private def unitArrow {X Y : TopCat.{u}} (f : X ⟶ Y) :
    Arrow.mk (unitMap X) ⟶ Arrow.mk (unitMap Y) :=
  Arrow.homMk (TopCat.toSSet.map f) (baseMap f)
    (SSet.KanComplex.nativeCoverUnit_naturality (TopCat.toSSet.map f))

/-- The existing functorial mapping-path map applied to the original unit square. -/
def unitTotalMap {X Y : TopCat.{u}} (f : X ⟶ Y) : unitTotal X ⟶ unitTotal Y :=
  SSet.KanWeakInterpolation.pathMap (unitArrow f)

private theorem unitTotalMap_projection_computation {X Y : TopCat.{u}} (f : X ⟶ Y) :
    unitTotalMap f ≫ unitProjection Y = unitProjection X ≫ baseMap f :=
  SSet.KanWeakInterpolation.pathMap_target (unitArrow f)

/-- The actual map retains the whole original base square. -/
theorem unitTotalMap_projection {X Y : TopCat.{u}} (f : X ⟶ Y) :
    unitTotalMap f ≫ unitProjection Y = unitProjection X ≫ baseMap f :=
  unitTotalMap_projection_computation f

private theorem unitTotalMap_retract_computation {X Y : TopCat.{u}} (f : X ⟶ Y) :
    unitTotalMap f ≫ SSet.mappingPathRetract (SSet.KanComplex.nativeCoverUnit (TopCat.toSSet.obj Y)) =
      SSet.mappingPathRetract (SSet.KanComplex.nativeCoverUnit (TopCat.toSSet.obj X)) ≫
        TopCat.toSSet.map f :=
  SSet.KanWeakInterpolation.pathMap_retract (unitArrow f)

/-- The actual map retains the original singular map through both fixed retracts. -/
theorem unitTotalMap_retract {X Y : TopCat.{u}} (f : X ⟶ Y) :
    unitTotalMap f ≫ SSet.mappingPathRetract (SSet.KanComplex.nativeCoverUnit (TopCat.toSSet.obj Y)) =
      SSet.mappingPathRetract (SSet.KanComplex.nativeCoverUnit (TopCat.toSSet.obj X)) ≫
        TopCat.toSSet.map f :=
  unitTotalMap_retract_computation f

/-- The target unit fibration pulled to the SAME source groupoid-nerve base. -/
abbrev commonTarget {X Y : TopCat.{u}} (f : X ⟶ Y) : SSet.{u} :=
  pullback (baseMap f) (unitProjection Y)

/-- The original second projection from that actual common-base pullback. -/
def commonTargetComparison {X Y : TopCat.{u}} (f : X ⟶ Y) : commonTarget f ⟶ unitTotal Y :=
  pullback.snd (baseMap f) (unitProjection Y)

/-- The actual common-base map of total spaces, with no supplied comparison model. -/
def commonTotalMap {X Y : TopCat.{u}} (f : X ⟶ Y) : unitTotal X ⟶ commonTarget f :=
  pullback.lift (unitProjection X) (unitTotalMap f) (unitTotalMap_projection f).symm

private theorem commonTotalMap_fst_computation {X Y : TopCat.{u}} (f : X ⟶ Y) :
    commonTotalMap f ≫ CategoryTheory.Limits.pullback.fst (baseMap f) (unitProjection Y) =
      unitProjection X :=
  CategoryTheory.Limits.pullback.lift_fst _ _ _

/-- The original first projection retains the source unit fibration over the common base. -/
theorem commonTotalMap_fst {X Y : TopCat.{u}} (f : X ⟶ Y) :
    commonTotalMap f ≫ CategoryTheory.Limits.pullback.fst (baseMap f) (unitProjection Y) =
      unitProjection X :=
  commonTotalMap_fst_computation f

private theorem commonTotalMap_snd_computation {X Y : TopCat.{u}} (f : X ⟶ Y) :
    commonTotalMap f ≫ commonTargetComparison f = unitTotalMap f :=
  pullback.lift_snd _ _ _

/-- The original second projection returns the original mapping-path map. -/
theorem commonTotalMap_snd {X Y : TopCat.{u}} (f : X ⟶ Y) :
    commonTotalMap f ≫ commonTargetComparison f = unitTotalMap f :=
  commonTotalMap_snd_computation f

private theorem commonTotalMap_original_computation {X Y : TopCat.{u}} (f : X ⟶ Y) :
    commonTotalMap f ≫
      (commonTargetComparison f ≫ SSet.mappingPathRetract
        (SSet.KanComplex.nativeCoverUnit (TopCat.toSSet.obj Y))) =
      SSet.mappingPathRetract (SSet.KanComplex.nativeCoverUnit (TopCat.toSSet.obj X)) ≫
        TopCat.toSSet.map f := by
  rw [← Category.assoc, commonTotalMap_snd, unitTotalMap_retract]

/-- The whole common-base map still has the exact original singular-map square. -/
theorem commonTotalMap_original {X Y : TopCat.{u}} (f : X ⟶ Y) :
    commonTotalMap f ≫
      (commonTargetComparison f ≫ SSet.mappingPathRetract
        (SSet.KanComplex.nativeCoverUnit (TopCat.toSSet.obj Y))) =
      SSet.mappingPathRetract (SSet.KanComplex.nativeCoverUnit (TopCat.toSSet.obj X)) ≫
        TopCat.toSSet.map f :=
  commonTotalMap_original_computation f

private theorem unitProjection_fibration (X : TopCat.{u}) : Fibration (unitProjection X) := by
  let : SSet.KanComplex (TopCat.toSSet.obj X) := TopCat.toSSet_obj_kanComplex X
  let : SSet.KanComplex (base X) :=
    SSet.kanComplex_nerve_of_groupoid (SSet.FundamentalGroupoid (TopCat.toSSet.obj X))
  change Fibration (SSet.mappingPathTarget (unitMap X))
  infer_instance

/-- The computed unit projection is a fibration, for its actual common-base consumers. -/
theorem unitProjection_isFibration (X : TopCat.{u}) : Fibration (unitProjection X) :=
  unitProjection_fibration X

private theorem unitRetract_weak (X : TopCat.{u}) :
    SSet.realizationWeakEquivalences (SSet.mappingPathRetract
      (SSet.KanComplex.nativeCoverUnit (TopCat.toSSet.obj X))) := by
  let : SSet.KanComplex (TopCat.toSSet.obj X) := TopCat.toSSet_obj_kanComplex X
  let : SSet.KanComplex (base X) :=
    SSet.kanComplex_nerve_of_groupoid (SSet.FundamentalGroupoid (TopCat.toSSet.obj X))
  exact (SSet.KanComplex.W_iff_realizationWeakEquivalence _).mp
    (SSet.KanComplex.W.of_mappingPathRetract (unitMap X))

private theorem commonTargetComparison_weak_computation
    {X Y : TopCat.{u}} [HSpace X] [HSpace Y]
    [PathConnectedSpace X] [PathConnectedSpace Y] (f : X ⟶ Y)
    (h1 : IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor 1).map f)) :
    SSet.realizationWeakEquivalences (commonTargetComparison f) := by
  let : Fibration (unitProjection Y) := unitProjection_fibration Y
  let : WeakEquivalence (baseMap f) := (weakEquivalence_iff _).mpr
    (TopCat.HSpaceHomologyOne.nerveBaseMap_mem_realizationWeakEquivalences_of_integralHomologyOne_isIso f h1)
  have h : WeakEquivalence (pullback.snd (baseMap f) (unitProjection Y)) :=
    IsRightProper.weakEquivalence_of_isPullback (IsPullback.of_hasPullback (baseMap f) (unitProjection Y))
  exact (weakEquivalence_iff _).mp h

/-- Integral H1 of the original map derives the actual common-base comparison's weak equivalence. -/
theorem commonTargetComparison_mem_realizationWeakEquivalences_of_integralH1
    {X Y : TopCat.{u}} [HSpace X] [HSpace Y]
    [PathConnectedSpace X] [PathConnectedSpace Y] (f : X ⟶ Y)
    (h1 : IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor 1).map f)) :
    SSet.realizationWeakEquivalences (commonTargetComparison f) :=
  commonTargetComparison_weak_computation f h1

private theorem homologyMap_isIso_of_weak {A B : SSet.{u}}
    [SSet.KanComplex A] [SSet.KanComplex B] (f : A ⟶ B)
    (hf : SSet.realizationWeakEquivalences f) (R : AddCommGrpCat.{u}) (n : ℕ) :
    IsIso (SSet.homologyMap f R n) := by
  let hw := (SSet.KanComplex.W_iff_realizationWeakEquivalence f).mpr hf
  let : QuasiIso (SSet.chainComplexMap f R) := hw.quasiIso_chainComplexMap R
  exact (_root_.quasiIsoAt_iff_isIso_homologyMap (SSet.chainComplexMap f R) n).mp
    (inferInstance : QuasiIsoAt (SSet.chainComplexMap f R) n)

/-- Ordinary integral homology in degree n and the original H1 comparison
derive homology isomorphism of the ACTUAL common-base total map. -/
theorem commonTotalMap_integralHomology_isIso
    {X Y : TopCat.{u}} [HSpace X] [HSpace Y]
    [PathConnectedSpace X] [PathConnectedSpace Y] (f : X ⟶ Y)
    (h1 : IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor 1).map f)) (n : ℕ)
    (hn : IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor n).map f)) :
    IsIso (SSet.homologyMap (commonTotalMap f)
      (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u}) n) := by
  let R : AddCommGrpCat.{u} := AlgebraicTopology.singularIntegralCoefficients
  let H := SSet.homologyFunctor R n
  let sf := TopCat.toSSet.map f
  let rX := SSet.mappingPathRetract (unitMap X)
  let rY := commonTargetComparison f ≫ SSet.mappingPathRetract (unitMap Y)
  let m := commonTotalMap f
  let : SSet.KanComplex (TopCat.toSSet.obj X) := TopCat.toSSet_obj_kanComplex X
  let : SSet.KanComplex (TopCat.toSSet.obj Y) := TopCat.toSSet_obj_kanComplex Y
  let : SSet.KanComplex (base X) :=
    SSet.kanComplex_nerve_of_groupoid (SSet.FundamentalGroupoid (TopCat.toSSet.obj X))
  let : SSet.KanComplex (base Y) :=
    SSet.kanComplex_nerve_of_groupoid (SSet.FundamentalGroupoid (TopCat.toSSet.obj Y))
  let : SSet.KanComplex (unitTotal X) := inferInstance
  let : SSet.KanComplex (unitTotal Y) := inferInstance
  let : Fibration (unitProjection Y) := unitProjection_fibration Y
  let : SSet.KanComplex (commonTarget f) := inferInstance
  have hrY : SSet.realizationWeakEquivalences rY :=
    SSet.realizationWeakEquivalences.comp_mem _ _
      (commonTargetComparison_mem_realizationWeakEquivalences_of_integralH1 f h1) (unitRetract_weak Y)
  let : IsIso (H.map rX) := homologyMap_isIso_of_weak rX (unitRetract_weak X) R n
  let : IsIso (H.map rY) := homologyMap_isIso_of_weak rY hrY R n
  let : IsIso (H.map sf) := hn
  have hs : H.map m ≫ H.map rY = H.map rX ≫ H.map sf :=
    (H.map_comp m rY).symm.trans
      ((congrArg H.map (commonTotalMap_original f)).trans (H.map_comp rX sf))
  let : IsIso (H.map m ≫ H.map rY) := hs.symm ▸ (inferInstance : IsIso (H.map rX ≫ H.map sf))
  exact (isIso_comp_right_iff (H.map m) (H.map rY)).mp inferInstance

end TopCat.HSpaceCommonUnitFibration

namespace TopCat.HSpaceCommonUnitFibration

private theorem unitProjection_eq_computation (X : TopCat.{u}) :
    unitProjection X = SSet.mappingPathTarget
      (SSet.KanComplex.nativeCoverUnit (TopCat.toSSet.obj X)) := by
  unfold unitProjection
  rfl

/-- The actual public projection is the original unit mapping-path target. -/
theorem unitProjection_eq (X : TopCat.{u}) :
    unitProjection X = SSet.mappingPathTarget
      (SSet.KanComplex.nativeCoverUnit (TopCat.toSSet.obj X)) :=
  unitProjection_eq_computation X

private theorem baseMap_eq_computation {X Y : TopCat.{u}} (f : X ⟶ Y) :
    baseMap f = CategoryTheory.nerveMap (SSet.mapFundamentalGroupoid (TopCat.toSSet.map f)) := by
  unfold baseMap
  rfl

/-- The actual public base map is the nerve of the original singular groupoid map. -/
theorem baseMap_eq {X Y : TopCat.{u}} (f : X ⟶ Y) :
    baseMap f = CategoryTheory.nerveMap (SSet.mapFundamentalGroupoid (TopCat.toSSet.map f)) :=
  baseMap_eq_computation f

end TopCat.HSpaceCommonUnitFibration

namespace TopCat.HSpaceCommonUnitFibration

/-- The original singular-map square preserves the actual unit constant-path sections. -/
theorem unitTotalMap_section {X Y : TopCat.{u}} (f : X ⟶ Y) :
    SSet.mappingPathSection (SSet.KanComplex.nativeCoverUnit (TopCat.toSSet.obj X)) ≫
        unitTotalMap f =
      TopCat.toSSet.map f ≫
        SSet.mappingPathSection (SSet.KanComplex.nativeCoverUnit (TopCat.toSSet.obj Y)) :=
  SSet.KanWeakInterpolation.pathMap_section (unitArrow f)

private theorem commonTargetComparison_eq_computation {X Y : TopCat.{u}} (f : X ⟶ Y) :
    commonTargetComparison f = pullback.snd (baseMap f) (unitProjection Y) := by
  unfold commonTargetComparison
  rfl

/-- The actual common-target comparison is the second projection of the original pullback. -/
theorem commonTargetComparison_eq {X Y : TopCat.{u}} (f : X ⟶ Y) :
    commonTargetComparison f = pullback.snd (baseMap f) (unitProjection Y) :=
  commonTargetComparison_eq_computation f

end TopCat.HSpaceCommonUnitFibration
