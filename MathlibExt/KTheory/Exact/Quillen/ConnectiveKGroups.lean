/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Quillen.ConnectiveKGroups.Basic
public import MathlibExt.KTheory.Exact.Quillen.KSpaceFunctorAllKiMap
public import MathlibExt.KTheory.Exact.Quillen.OriginalCanonicalKiZeroFunctorLaws
public import MathlibExt.KTheory.Exact.Quillen.QuillenQSZigzagComponentsMixedNaturality
public import MathlibExt.KTheory.Waldhausen.K0.Exact
public import MathlibExt.Topology.Homotopy.WeaklyPointedLoopShiftNaturality

/-!
# Generic connective Quillen groups and their actual chosen roots

The canonical topology loop-shift theorem retains the actual chosen root.
The positive loop map and its exact own-unit path reuse the existing
weakly pointed topology APIs, including the proved joint contraction recipe.

For a generic exact category, `rawCarrier` is the original cube carrier of
`NQKSpace`. `groupCarrier`, `rawToGroup` and `bqShift` give its actual group
convention and the canonical next-BQ comparison. The complete original
Waldhausen and exact K-zero dictionaries agree on every zero class.

The commutative and additive conventions retain the original group data.
Every `groupMap`, `bqMap` and `additiveMap` follows the original exact-functor
map and chosen zero path, with whole-map dictionary squares, identity,
composition and natural-isomorphism laws.
-/

public section
noncomputable section

open CategoryTheory Limits Topology
open scoped ContinuousMap unitInterval Topology.Homotopy

universe uX uY uC vC uD vD uE vE

namespace AlgebraicKTheory.ConnectiveKGroups

private theorem mapHomOfEq_congr
    {X : Type uX} {Y : Type uY} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (f g : C(X, Y)) (hf : f x = y) (hg : g x = y)
    (h : f = g) (n : ℕ) (a : HomotopyGroup.Pi (n + 1) X x) :
    HomotopyGroup.mapHomOfEq f hf n a = HomotopyGroup.mapHomOfEq g hg n a := by
  cases h
  rfl

private theorem basepointChange_sourceCast
    {Y : Type uY} [TopologicalSpace Y] (n : ℕ) {a a' b : Y}
    (p : Path a b) (h : a' = a) (x : HomotopyGroup.Pi (n + 1) Y a') :
    TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of Y) (p.cast h rfl) x =
      TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of Y) p (h ▸ x) := by
  cases h
  rfl

private theorem loopComponents_fundamental
    {X : Type uX} {Y : Type uY} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (f : ContinuousMap.WeaklyPointed x y)
    (a : ZerothHomotopy (LoopSpace X x)) :
    loopComponentsEquivFundamentalGroup Y y (f.loopComponentsMap a) =
      basedFundamentalGroupMap f.hom f.rootPath
        (loopComponentsEquivFundamentalGroup X x a) :=
  (loopComponentsEquivFundamentalGroup Y y).apply_symm_apply _

private theorem rootedIdentityValue
    {Y : Type uY} [TopologicalSpace Y] (n : ℕ) {x : Y}
    (f : C(Y, Y)) (p : Path (f x) x) (hF : f = ContinuousMap.id Y)
    (hP : (p.cast (DFunLike.congr_fun hF x).symm rfl).Homotopic (Path.refl x))
    (a : HomotopyGroup.Pi (n + 1) Y x) :
    TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of Y) p
      (HomotopyGroup.map f a) = a := by
  cases hF
  have hRoot : p.Homotopic (Path.refl x) := hP
  exact (DFunLike.congr_fun
    (TopCat.homotopyGroupBasepointChangeMulEquiv_eq_of_homotopic n (TopCat.of Y) hRoot)
    (HomotopyGroup.map (ContinuousMap.id Y) a)).trans
      ((DFunLike.congr_fun
        (TopCat.homotopyGroupBasepointChangeMulEquiv_refl n (TopCat.of Y) x)
        (HomotopyGroup.map (ContinuousMap.id Y) a)).trans (HomotopyGroup.map_id a))

private def transportMulEquivSource
    {A : Type uX} {B : Type uY} [Mul B] (G H : Group A) (h : G = H)
    (e : letI := H; A ≃* B) : letI := G; A ≃* B := by
  cases h
  exact e

private theorem transportMulEquivSource_apply
    {A : Type uX} {B : Type uY} [Mul B] (G H : Group A) (h : G = H)
    (e : letI := H; A ≃* B) (x : A) :
    transportMulEquivSource G H h e x = e x := by
  cases h
  rfl

section ExactCategories

open CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen.SConstruction
open AlgebraicKTheory.QuillenQSZigzagGroupNaturality.Internal

variable (C : Type uC) [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

/-- The original Waldhausen dictionary derived from this exact category. -/
local instance connectiveWaldhausen : WaldhausenCategory C :=
  ExactCategory.waldhausenCategory C

private theorem qLeg_components_fundamental
    (a : ZerothHomotopy (quillenStageGridDiagonalKSpace C)) :
    loopComponentsEquivFundamentalGroup (NQReal C) (NQReal.basepoint C)
        (quillenStageGridToNQPiZeroEquiv C a) =
      quillenStageGridToNQFundamentalMulEquiv C
        (loopComponentsEquivFundamentalGroup (quillenStageGridDiagonalReal C)
          (quillenStageGridDiagonalReal.basepoint C) a) := by
  have h := loopComponents_fundamental (quillenStageGridToNQWeaklyPointed (C := C)) a
  exact (congrArg (loopComponentsEquivFundamentalGroup (NQReal C) (NQReal.basepoint C))
    (quillenStageGridToNQPiZeroEquiv_apply C a)).trans h

private theorem stageLeg_components_fundamental
    (a : ZerothHomotopy (quillenStageGridDiagonalKSpace C)) :
    loopComponentsEquivFundamentalGroup (stageWeakDiagonalReal C)
        (stageWeakDiagonalReal.basepoint C) (quillenStageGridToStagePiZeroEquiv C a) =
      quillenStageGridToStageFundamentalMulEquiv C
        (loopComponentsEquivFundamentalGroup (quillenStageGridDiagonalReal C)
          (quillenStageGridDiagonalReal.basepoint C) a) := by
  have h := loopComponents_fundamental (quillenStageGridToStageWeaklyPointed (C := C)) a
  exact (congrArg (loopComponentsEquivFundamentalGroup (stageWeakDiagonalReal C)
    (stageWeakDiagonalReal.basepoint C))
    (quillenStageGridToStagePiZeroEquiv_apply C a)).trans h

private theorem zeroDictionaryReconciliationComputed
    (a : ZerothHomotopy (NQKSpace C)) :
    NQRealizedFundamentalK0MulEquiv C
        (loopComponentsEquivFundamentalGroup (NQReal C) (NQReal.basepoint C) a) =
      Multiplicative.ofAdd (NQKSpacePiZeroEquivK0 C a) := by
  let Q0 := quillenStageGridToNQPiZeroEquiv C
  let S0 := quillenStageGridToStagePiZeroEquiv C
  let Q1 := quillenStageGridToNQFundamentalMulEquiv C
  let S1 := quillenStageGridToStageFundamentalMulEquiv C
  let g := Q0.symm a
  let gridFund := loopComponentsEquivFundamentalGroup (quillenStageGridDiagonalReal C)
    (quillenStageGridDiagonalReal.basepoint C) g
  let sourceFund := loopComponentsEquivFundamentalGroup (NQReal C) (NQReal.basepoint C) a
  have hQ : Q1 gridFund = sourceFund :=
    (qLeg_components_fundamental C g).symm.trans
      (congrArg (loopComponentsEquivFundamentalGroup (NQReal C) (NQReal.basepoint C))
        (Q0.apply_symm_apply a))
  have hQinv : Q1.symm sourceFund = gridFund := by
    apply Q1.injective
    exact (Q1.apply_symm_apply sourceFund).trans hQ.symm
  have hS : S1 gridFund =
      loopComponentsEquivFundamentalGroup (stageWeakDiagonalReal C)
        (stageWeakDiagonalReal.basepoint C) (S0 g) :=
    (stageLeg_components_fundamental C g).symm
  have hStage : stageWeakDiagonalRealizedFundamentalK0MulEquiv C
      (loopComponentsEquivFundamentalGroup (stageWeakDiagonalReal C)
        (stageWeakDiagonalReal.basepoint C) (S0 g)) =
        Multiplicative.ofAdd (stageWeakDiagonalKSpacePiZeroEquivK0 C (S0 g)) :=
    (congrArg Multiplicative.ofAdd
      (stageWeakDiagonalKSpacePiZeroEquivK0_apply C (S0 g))).symm
  change stageWeakDiagonalRealizedFundamentalK0MulEquiv C (S1 (Q1.symm sourceFund)) = _
  exact (congrArg (fun x => stageWeakDiagonalRealizedFundamentalK0MulEquiv C (S1 x))
    hQinv).trans
      ((congrArg (stageWeakDiagonalRealizedFundamentalK0MulEquiv C) hS).trans
        (hStage.trans (congrArg Multiplicative.ofAdd (NQKSpacePiZeroEquivK0_apply C a).symm)))

/-- The two original Quillen K-zero dictionaries evaluate the same complete loop class. -/
theorem zeroDictionary_reconciliation
    (a : ZerothHomotopy (NQKSpace C)) :
    NQRealizedFundamentalK0MulEquiv C
        (loopComponentsEquivFundamentalGroup (NQReal C) (NQReal.basepoint C) a) =
      Multiplicative.ofAdd (NQKSpacePiZeroEquivK0 C a) :=
  zeroDictionaryReconciliationComputed C a

/-- Degree zero uses the original fundamental group; positive degrees retain the original cubes. -/
abbrev groupCarrier : ℕ → Type (max uC vC)
  | 0 => FundamentalGroup (NQReal C) (NQReal.basepoint C)
  | n + 1 => HomotopyGroup.Pi (n + 1) (NQKSpace C) (zeroLoop C)

/-- The group convention keeps the existing fundamental and positive stock group laws. -/
def groupStructure : (n : ℕ) → Group (groupCarrier C n)
  | 0 => inferInstance
  | n + 1 => NQKSpaceOriginalPositiveGroup C n (zeroLoop C)

private theorem groupStructureZeroComputed :
    groupStructure C 0 =
      (inferInstance : Group (FundamentalGroup (NQReal C) (NQReal.basepoint C))) := rfl

/-- Degree zero retains the actual original fundamental-group structure at the chosen zero. -/
theorem groupStructure_zero_value :
    groupStructure C 0 =
      (inferInstance : Group (FundamentalGroup (NQReal C) (NQReal.basepoint C))) :=
  groupStructureZeroComputed C

private theorem groupStructureSuccComputed (n : ℕ) :
    groupStructure C (n + 1) = NQKSpaceOriginalPositiveGroup C n (zeroLoop C) := rfl

/-- Every positive degree retains the entire original named cube group structure. -/
theorem groupStructure_succ_value (n : ℕ) :
    groupStructure C (n + 1) = NQKSpaceOriginalPositiveGroup C n (zeroLoop C) :=
  groupStructureSuccComputed C n

/-- The next-BQ convention uses the actual fundamental group in degree one. -/
abbrev bqCarrier : ℕ → Type (max uC vC)
  | 0 => FundamentalGroup (NQReal C) (NQReal.basepoint C)
  | n + 1 => HomotopyGroup.Pi (n + 2) (NQReal C) (NQReal.basepoint C)

/-- The actual next-BQ group laws, with no group law added to raw pi-zero. -/
def bqGroupStructure : (n : ℕ) → Group (bqCarrier C n)
  | 0 => inferInstance
  | n + 1 => HomotopyGroup.group (X := NQReal C) (x := NQReal.basepoint C) (Fin (n + 2))

/-- Raw loop components are compared with the actual fundamental group at the same zero. -/
def rawToGroup : (n : ℕ) → rawCarrier C n ≃ groupCarrier C n
  | 0 => (HomotopyGroup.pi0EquivZerothHomotopy
      (X := NQKSpace C) (x := zeroLoop C)).trans
        (loopComponentsEquivFundamentalGroup (NQReal C) (NQReal.basepoint C))
  | _ + 1 => Equiv.refl _

private theorem rawToGroupZeroComputed (a : rawCarrier C 0) :
    rawToGroup C 0 a =
      loopComponentsEquivFundamentalGroup (NQReal C) (NQReal.basepoint C)
        (HomotopyGroup.pi0EquivZerothHomotopy (X := NQKSpace C) (x := zeroLoop C) a) := rfl

/-- The raw zero comparison is the literal component/fundamental dictionary at the same zero. -/
theorem rawToGroup_zero_apply (a : rawCarrier C 0) :
    rawToGroup C 0 a =
      loopComponentsEquivFundamentalGroup (NQReal C) (NQReal.basepoint C)
        (HomotopyGroup.pi0EquivZerothHomotopy (X := NQKSpace C) (x := zeroLoop C) a) :=
  rawToGroupZeroComputed C a

private theorem rawToGroupSuccComputed (n : ℕ) (a : rawCarrier C (n + 1)) :
    rawToGroup C (n + 1) a = a := rfl

/-- Positive raw and group conventions retain the identical original cube class. -/
theorem rawToGroup_succ_apply (n : ℕ) (a : rawCarrier C (n + 1)) :
    rawToGroup C (n + 1) a = a := rawToGroupSuccComputed C n a

private def bqShiftComputed : (n : ℕ) →
    letI := groupStructure C n
    letI := bqGroupStructure C n
    groupCarrier C n ≃* bqCarrier C n
  | 0 => MulEquiv.refl _
  | n + 1 => transportMulEquivSource
      (NQKSpaceOriginalPositiveGroup C n (zeroLoop C))
      (HomotopyGroup.group (X := NQKSpace C) (x := zeroLoop C) (Fin (n + 1)))
      (NQKSpaceOriginalPositiveGroup_value C n (zeroLoop C))
      (HomotopyGroup.loopShiftMulEquiv n (NQReal C) (NQReal.basepoint C))

/-- The all-degree canonical loop shift keeps the original positive stock comparison. -/
def bqShift (n : ℕ) :
    letI := groupStructure C n
    letI := bqGroupStructure C n
    groupCarrier C n ≃* bqCarrier C n :=
  bqShiftComputed C n

private theorem bqShiftSuccApplyComputed (n : ℕ) (a : groupCarrier C (n + 1)) :
    bqShift C (n + 1) a =
      HomotopyGroup.loopShiftMulEquiv n (NQReal C) (NQReal.basepoint C) a :=
  transportMulEquivSource_apply
    (NQKSpaceOriginalPositiveGroup C n (zeroLoop C))
    (HomotopyGroup.group (X := NQKSpace C) (x := zeroLoop C) (Fin (n + 1)))
    (NQKSpaceOriginalPositiveGroup_value C n (zeroLoop C))
    (HomotopyGroup.loopShiftMulEquiv n (NQReal C) (NQReal.basepoint C)) a

/-- Every positive class follows the unchanged original stock shift function. -/
theorem bqShift_succ_apply (n : ℕ) (a : groupCarrier C (n + 1)) :
    bqShift C (n + 1) a =
      HomotopyGroup.loopShiftMulEquiv n (NQReal C) (NQReal.basepoint C) a :=
  bqShiftSuccApplyComputed C n a

/-- The original raw zero dictionary into exact-derived Waldhausen K-zero. -/
def rawWaldhausenK0Equiv : rawCarrier C 0 ≃ WaldhausenKTheory.K0 C :=
  (HomotopyGroup.pi0EquivZerothHomotopy (X := NQKSpace C) (x := zeroLoop C)).trans
    (NQKSpacePiZeroEquivK0 C)

/-- The original raw zero dictionary then follows the literal canonical exact-K-zero isomorphism. -/
def rawExactK0Equiv : rawCarrier C 0 ≃ AlgebraicKTheory.K0 C :=
  (rawWaldhausenK0Equiv C).trans
    (CategoryTheory.Iso.addCommGroupIsoToAddEquiv (WaldhausenKTheory.K0.exactIso C)).toEquiv

private theorem rawExactK0ValueComputed (a : rawCarrier C 0) :
    rawExactK0Equiv C a = WaldhausenKTheory.K0.toExact C (rawWaldhausenK0Equiv C a) := rfl

/-- The raw exact dictionary follows the literal canonical forward
on the original Waldhausen class. -/
theorem rawExactK0Equiv_apply (a : rawCarrier C 0) :
    rawExactK0Equiv C a = WaldhausenKTheory.K0.toExact C (rawWaldhausenK0Equiv C a) :=
  rawExactK0ValueComputed C a

/-- The source group convention has the same original Waldhausen K-zero group dictionary. -/
def groupWaldhausenK0Equiv :
    @MulEquiv (groupCarrier C 0) (Multiplicative (WaldhausenKTheory.K0 C))
      (groupStructure C 0).toMulOneClass.toMulOne.toMul inferInstance :=
  NQRealizedFundamentalK0MulEquiv C

/-- The source zero group is the canonical algebraic exact K-zero
through its literal isomorphism. -/
def groupExactK0Equiv :
    @AddEquiv (Additive (groupCarrier C 0)) (AlgebraicKTheory.K0 C)
      (@Additive.add (groupCarrier C 0) (groupStructure C 0).toMulOneClass.toMulOne.toMul)
      inferInstance :=
  (MulEquiv.toAdditiveLeft (NQRealizedFundamentalK0MulEquiv C)).trans
    (CategoryTheory.Iso.addCommGroupIsoToAddEquiv (WaldhausenKTheory.K0.exactIso C))

variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
  (F : C ⥤ D) [F.Additive] [F.IsExact]

private theorem originalFunctorUnitPathComputed :
    NQKSpaceFunctorKiUnitRootPath F =
      (ContinuousMap.WeaklyPointed.loopUnitRootPath (NQRealFunctorWeaklyPointed F)).cast
        (DFunLike.congr_fun (NQKSpaceFunctorMap_eq_loopMap F) (zeroLoop C)) rfl := by
  rw [ContinuousMap.WeaklyPointed.originalLoopOwnUnit_eq201]
  apply Path.ext
  funext t
  exact congrArg
    (fun p : Path (NQKSpaceFunctorMap F (zeroLoop C)) (zeroLoop D) => p t)
    (NQKSpaceFunctorKiUnitRootPath_eq_rootUnitContraction F)

/-- The designated K-map unit path is the same original root contraction,
with only its source cast. -/
theorem originalFunctorUnitPath :
    NQKSpaceFunctorKiUnitRootPath F =
      (ContinuousMap.WeaklyPointed.loopUnitRootPath (NQRealFunctorWeaklyPointed F)).cast
        (DFunLike.congr_fun (NQKSpaceFunctorMap_eq_loopMap F) (zeroLoop C)) rfl :=
  originalFunctorUnitPathComputed C F

private theorem originalPositiveMapComputed (n : ℕ) (a : rawCarrier C (n + 1)) :
    NQKSpaceFunctorPositiveKiMap F n a =
      ContinuousMap.WeaklyPointed.positiveHomotopyGroupMap n
      (⟨(NQRealFunctorWeaklyPointed F).loopMap,
        ContinuousMap.WeaklyPointed.loopUnitRootPath (NQRealFunctorWeaklyPointed F)⟩ :
        ContinuousMap.WeaklyPointed (zeroLoop C) (zeroLoop D)) a := by
  let f := NQRealFunctorWeaklyPointed F
  let M := NQKSpaceFunctorMap F
  let hMap : M = f.loopMap := NQKSpaceFunctorMap_eq_loopMap F
  let hStart : M (zeroLoop C) = f.loopMap (zeroLoop C) := DFunLike.congr_fun hMap (zeroLoop C)
  have hUnit : NQKSpaceFunctorKiUnitRootPath F =
      (ContinuousMap.WeaklyPointed.loopUnitRootPath f).cast hStart rfl :=
    originalFunctorUnitPath C F
  have hClass : hStart ▸ HomotopyGroup.map M a = HomotopyGroup.map f.loopMap a :=
    (HomotopyGroup.mapHomOfEq_apply M hStart n a).symm.trans
      ((mapHomOfEq_congr M f.loopMap hStart rfl hMap n a).trans
        (HomotopyGroup.mapHomOfEq_apply f.loopMap rfl n a))
  have hNative := NQKSpaceFunctorPositiveKiMap_apply F n a
  change NQKSpaceFunctorPositiveKiMap F n a =
    TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of (NQKSpace D))
      (NQKSpaceFunctorKiUnitRootPath F) (HomotopyGroup.map M a) at hNative
  rw [ContinuousMap.WeaklyPointed.positiveHomotopyGroupMap_apply]
  change NQKSpaceFunctorPositiveKiMap F n a =
    TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of (NQKSpace D))
      (ContinuousMap.WeaklyPointed.loopUnitRootPath f) (HomotopyGroup.map f.loopMap a)
  exact hNative.trans
    ((congrArg (fun p => TopCat.homotopyGroupBasepointChangeMulEquiv n
        (TopCat.of (NQKSpace D)) p (HomotopyGroup.map M a)) hUnit).trans
      ((basepointChange_sourceCast n (ContinuousMap.WeaklyPointed.loopUnitRootPath f) hStart
        (HomotopyGroup.map M a)).trans
        (congrArg (TopCat.homotopyGroupBasepointChangeMulEquiv n
          (TopCat.of (NQKSpace D)) (ContinuousMap.WeaklyPointed.loopUnitRootPath f)) hClass)))

/-- The positive K-map uses the same whole rooted loop program and the same designated unit path. -/
theorem originalPositiveMap (n : ℕ) (a : rawCarrier C (n + 1)) :
    NQKSpaceFunctorPositiveKiMap F n a =
      ContinuousMap.WeaklyPointed.positiveHomotopyGroupMap n
      (⟨(NQRealFunctorWeaklyPointed F).loopMap,
        ContinuousMap.WeaklyPointed.loopUnitRootPath (NQRealFunctorWeaklyPointed F)⟩ :
        ContinuousMap.WeaklyPointed (zeroLoop C) (zeroLoop D)) a :=
  originalPositiveMapComputed C F n a

/-- The positive loop shift square follows the literal original Quillen functor map
and zero root. -/
theorem originalPositiveShift_naturality (n : ℕ) (a : rawCarrier C (n + 1)) :
    HomotopyGroup.loopShiftMulEquiv n (NQReal D) (NQReal.basepoint D)
        (NQKSpaceFunctorPositiveKiMap F n a) =
      TopCat.homotopyGroupBasepointChangeMulEquiv (n + 1) (TopCat.of (NQReal D))
        (NQRealFunctorWeaklyPointed F).rootPath
        (HomotopyGroup.map (NQRealFunctorWeaklyPointed F).hom
          (HomotopyGroup.loopShiftMulEquiv n (NQReal C) (NQReal.basepoint C) a)) :=
  (congrArg (HomotopyGroup.loopShiftMulEquiv n (NQReal D) (NQReal.basepoint D))
    (originalPositiveMap C F n a)).trans
      (HomotopyGroup.loopShiftMulEquiv_rooted_naturality n (NQRealFunctorWeaklyPointed F) a)

private def groupMapComputed : (n : ℕ) →
    letI := groupStructure C n
    letI := groupStructure D n
    groupCarrier C n →* groupCarrier D n
  | 0 => basedFundamentalGroupMap (NQRealFunctorWeaklyPointed F).hom
      (NQRealFunctorWeaklyPointed F).rootPath
  | n + 1 => NQKSpaceFunctorPositiveKiMap F n

/-- Every source K-group map is the actual additive exact-functor map
with its original zero path. -/
def groupMap (n : ℕ) :
    letI := groupStructure C n
    letI := groupStructure D n
    groupCarrier C n →* groupCarrier D n :=
  groupMapComputed C F n

private theorem groupMapZeroComputed (g : groupCarrier C 0) :
    groupMap C F 0 g = basedFundamentalGroupMap (NQRealFunctorWeaklyPointed F).hom
      (NQRealFunctorWeaklyPointed F).rootPath g := rfl

/-- Degree zero retains the original whole realization map and the original chosen-zero path. -/
theorem groupMap_zero_apply (g : groupCarrier C 0) :
    groupMap C F 0 g = basedFundamentalGroupMap (NQRealFunctorWeaklyPointed F).hom
      (NQRealFunctorWeaklyPointed F).rootPath g := groupMapZeroComputed C F g

private theorem groupMapSuccComputed (n : ℕ) (a : groupCarrier C (n + 1)) :
    groupMap C F (n + 1) a = NQKSpaceFunctorPositiveKiMap F n a := rfl

/-- Every positive group map is the identical original positive homomorphism on each class. -/
theorem groupMap_succ_apply (n : ℕ) (a : groupCarrier C (n + 1)) :
    groupMap C F (n + 1) a = NQKSpaceFunctorPositiveKiMap F n a :=
  groupMapSuccComputed C F n a

private def bqMapComputed : (n : ℕ) →
    letI := bqGroupStructure C n
    letI := bqGroupStructure D n
    bqCarrier C n →* bqCarrier D n
  | 0 => basedFundamentalGroupMap (NQRealFunctorWeaklyPointed F).hom
      (NQRealFunctorWeaklyPointed F).rootPath
  | n + 1 =>
      (TopCat.homotopyGroupBasepointChangeMulEquiv (n + 1) (TopCat.of (NQReal D))
        (NQRealFunctorWeaklyPointed F).rootPath).toMonoidHom.comp
          (HomotopyGroup.mapHom (NQRealFunctorWeaklyPointed F).hom)

/-- The next-BQ map follows the same original realization and original zero-comparison path. -/
def bqMap (n : ℕ) :
    letI := bqGroupStructure C n
    letI := bqGroupStructure D n
    bqCarrier C n →* bqCarrier D n :=
  bqMapComputed C F n

private theorem bqShiftNaturalityComputed (n : ℕ) (a : groupCarrier C n) :
    bqShift D n (groupMap C F n a) = bqMap C F n (bqShift C n a) := by
  cases n with
  | zero => rfl
  | succ n =>
      have hGroup : groupMap C F (n + 1) a = NQKSpaceFunctorPositiveKiMap F n a := rfl
      have hBQ (x : bqCarrier C (n + 1)) : bqMap C F (n + 1) x =
          TopCat.homotopyGroupBasepointChangeMulEquiv (n + 1) (TopCat.of (NQReal D))
            (NQRealFunctorWeaklyPointed F).rootPath
            (HomotopyGroup.map (NQRealFunctorWeaklyPointed F).hom x) := rfl
      exact (bqShift_succ_apply D n (groupMap C F (n + 1) a)).trans
        ((congrArg (HomotopyGroup.loopShiftMulEquiv n (NQReal D) (NQReal.basepoint D))
          hGroup).trans
          ((originalPositiveShift_naturality C F n a).trans
            ((congrArg (fun x =>
              TopCat.homotopyGroupBasepointChangeMulEquiv (n + 1) (TopCat.of (NQReal D))
                (NQRealFunctorWeaklyPointed F).rootPath
                (HomotopyGroup.map (NQRealFunctorWeaklyPointed F).hom x))
              (bqShift_succ_apply C n a)).symm.trans
                (hBQ (bqShift C (n + 1) a)).symm)))

/-- Every degree, including zero, retains the canonical source/BQ shift and actual functor maps. -/
theorem bqShift_naturality (n : ℕ) (a : groupCarrier C n) :
    bqShift D n (groupMap C F n a) = bqMap C F n (bqShift C n a) :=
  bqShiftNaturalityComputed C F n a

/-- The source/BQ square is equality of the complete original homomorphisms in every degree. -/
theorem bqShift_map (n : ℕ) :
    letI := groupStructure C n
    letI := groupStructure D n
    letI := bqGroupStructure C n
    letI := bqGroupStructure D n
    (bqShift D n).toMonoidHom.comp (groupMap C F n) =
      (bqMap C F n).comp (bqShift C n).toMonoidHom := by
  letI := groupStructure C n
  letI := groupStructure D n
  letI := bqGroupStructure C n
  letI := bqGroupStructure D n
  apply MonoidHom.ext
  exact bqShift_naturality C F n

private theorem originalComponentsFundComputed (a : ZerothHomotopy (NQKSpace C)) :
    loopComponentsEquivFundamentalGroup (NQReal D) (NQReal.basepoint D)
        (ZerothHomotopy.lift
          (fun gamma : NQKSpace C => ZerothHomotopy.mk (NQKSpaceFunctorMap F gamma))
          (fun {_ _} p => ZerothHomotopy.sound (p.map (NQKSpaceFunctorMap F).continuous)) a) =
      basedFundamentalGroupMap (NQRealFunctorWeaklyPointed F).hom
        (NQRealFunctorWeaklyPointed F).rootPath
        (loopComponentsEquivFundamentalGroup (NQReal C) (NQReal.basepoint C) a) := by
  induction a using ZerothHomotopy.rec with
  | mk gamma =>
      change loopComponentsEquivFundamentalGroup (NQReal D) (NQReal.basepoint D)
          (ZerothHomotopy.mk (NQKSpaceFunctorMap F gamma)) = _
      let gammaC : LoopSpace (NQReal C) (NQReal.basepoint C) := gamma
      let gammaD : LoopSpace (NQReal D) (NQReal.basepoint D) := NQKSpaceFunctorMap F gamma
      have hC := loopComponentsEquivFundamentalGroup_mk gammaC
      have hD := loopComponentsEquivFundamentalGroup_mk gammaD
      have hFund := basedFundamentalGroupMap_mk (NQRealFunctorWeaklyPointed F).hom
        (NQRealFunctorWeaklyPointed F).rootPath gammaC
      exact hD.trans
        ((congrArg
          (fun gamma : LoopSpace (NQReal D) (NQReal.basepoint D) =>
            FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk gamma))
          (NQKSpaceFunctorMap_apply F gamma)).trans
            (hFund.symm.trans
              (congrArg (basedFundamentalGroupMap (NQRealFunctorWeaklyPointed F).hom
                (NQRealFunctorWeaklyPointed F).rootPath) hC.symm)))

private theorem rawToGroupNaturalityComputed (n : ℕ) (a : rawCarrier C n) :
    rawToGroup D n (NQKSpaceFunctorKiMap F n a) =
      groupMap C F n (rawToGroup C n a) := by
  cases n with
  | zero =>
      let c := HomotopyGroup.pi0EquivZerothHomotopy
        (X := NQKSpace C) (x := zeroLoop C) a
      have h := congrArg
        (loopComponentsEquivFundamentalGroup (NQReal D) (NQReal.basepoint D))
        (NQKSpaceFunctorKiMap_zero_components F a)
      exact h.trans (originalComponentsFundComputed C F c)
  | succ n => exact NQKSpaceFunctorKiMap_succ_eq_positive F n a

/-- Raw cube classes and the actual group convention follow the same original map
in every degree. -/
theorem rawToGroup_naturality (n : ℕ) (a : rawCarrier C n) :
    rawToGroup D n (NQKSpaceFunctorKiMap F n a) =
      groupMap C F n (rawToGroup C n a) :=
  rawToGroupNaturalityComputed C F n a

/-- The complete raw-to-BQ comparison is the component dictionary in degree zero
and the original stock loop shift in every positive degree. -/
def rawToBQ (n : ℕ) : rawCarrier C n ≃ bqCarrier C n := by
  letI := groupStructure C n
  letI := bqGroupStructure C n
  exact (rawToGroup C n).trans (bqShift C n).toEquiv

private theorem rawToBQValueComputed (n : ℕ) (a : rawCarrier C n) :
    rawToBQ C n a = bqShift C n (rawToGroup C n a) := rfl

/-- The complete raw/BQ comparison evaluates the original source comparison and canonical shift. -/
theorem rawToBQ_apply (n : ℕ) (a : rawCarrier C n) :
    rawToBQ C n a = bqShift C n (rawToGroup C n a) := rawToBQValueComputed C n a

private theorem rawToBQNaturalityComputed (n : ℕ) (a : rawCarrier C n) :
    rawToBQ D n (NQKSpaceFunctorKiMap F n a) =
      bqMap C F n (rawToBQ C n a) :=
  (congrArg (bqShift D n) (rawToGroup_naturality C F n a)).trans
    (bqShift_naturality C F n (rawToGroup C n a))

/-- The whole raw/BQ triangle retains the original exact-functor realization and zero path. -/
theorem rawToBQ_naturality (n : ℕ) (a : rawCarrier C n) :
    rawToBQ D n (NQKSpaceFunctorKiMap F n a) =
      bqMap C F n (rawToBQ C n a) :=
  rawToBQNaturalityComputed C F n a

private theorem rawWaldhausenK0NaturalityComputed (a : rawCarrier C 0) :
    rawWaldhausenK0Equiv D (NQKSpaceFunctorKiMap F 0 a) =
      WaldhausenKTheory.K0.map F (rawWaldhausenK0Equiv C a) :=
  NQKSpaceFunctorKiMap_zero_K0_naturality F a

/-- The original raw zero dictionary commutes with the actual Waldhausen K-zero map. -/
theorem rawWaldhausenK0Equiv_naturality (a : rawCarrier C 0) :
    rawWaldhausenK0Equiv D (NQKSpaceFunctorKiMap F 0 a) =
      WaldhausenKTheory.K0.map F (rawWaldhausenK0Equiv C a) :=
  rawWaldhausenK0NaturalityComputed C F a

private theorem rawExactK0NaturalityComputed (a : rawCarrier C 0) :
    rawExactK0Equiv D (NQKSpaceFunctorKiMap F 0 a) =
      AlgebraicKTheory.K0.map F (rawExactK0Equiv C a) := by
  change WaldhausenKTheory.K0.toExact D
      (rawWaldhausenK0Equiv D (NQKSpaceFunctorKiMap F 0 a)) =
    AlgebraicKTheory.K0.map F
      (WaldhausenKTheory.K0.toExact C (rawWaldhausenK0Equiv C a))
  exact (congrArg (WaldhausenKTheory.K0.toExact D)
    (rawWaldhausenK0Equiv_naturality C F a)).trans
      (DFunLike.congr_fun (WaldhausenKTheory.K0.toExact_naturality C F)
        (rawWaldhausenK0Equiv C a))

/-- The canonical exact-K-zero dictionary commutes with the actual additive exact-functor map. -/
theorem rawExactK0Equiv_naturality (a : rawCarrier C 0) :
    rawExactK0Equiv D (NQKSpaceFunctorKiMap F 0 a) =
      AlgebraicKTheory.K0.map F (rawExactK0Equiv C a) :=
  rawExactK0NaturalityComputed C F a

private theorem rawGroupWaldhausenReconciliationComputed (a : rawCarrier C 0) :
    groupWaldhausenK0Equiv C (rawToGroup C 0 a) =
      Multiplicative.ofAdd (rawWaldhausenK0Equiv C a) :=
  zeroDictionary_reconciliation C
    (HomotopyGroup.pi0EquivZerothHomotopy (X := NQKSpace C) (x := zeroLoop C) a)

/-- The original raw and group Waldhausen dictionaries reconcile on every complete zero class. -/
theorem rawGroupWaldhausenK0_reconciliation (a : rawCarrier C 0) :
    groupWaldhausenK0Equiv C (rawToGroup C 0 a) =
      Multiplicative.ofAdd (rawWaldhausenK0Equiv C a) :=
  rawGroupWaldhausenReconciliationComputed C a

private theorem rawGroupExactReconciliationComputed (a : rawCarrier C 0) :
    groupExactK0Equiv C (Additive.ofMul (rawToGroup C 0 a)) = rawExactK0Equiv C a :=
  congrArg (fun x => WaldhausenKTheory.K0.toExact C (Multiplicative.toAdd x))
    (rawGroupWaldhausenK0_reconciliation C a)

/-- The two canonical exact-K-zero dictionaries reconcile
through the same original Waldhausen map. -/
theorem rawGroupExactK0_reconciliation (a : rawCarrier C 0) :
    groupExactK0Equiv C (Additive.ofMul (rawToGroup C 0 a)) = rawExactK0Equiv C a :=
  rawGroupExactReconciliationComputed C a

private theorem groupWaldhausenK0NaturalityComputed (g : groupCarrier C 0) :
    groupWaldhausenK0Equiv D (groupMap C F 0 g) =
      Multiplicative.ofAdd
        (WaldhausenKTheory.K0.map F (Multiplicative.toAdd (groupWaldhausenK0Equiv C g))) := by
  let a := (rawToGroup C 0).symm g
  have h := (rawToGroup C 0).apply_symm_apply g
  have hD := rawGroupWaldhausenK0_reconciliation D (NQKSpaceFunctorKiMap F 0 a)
  have hC := rawGroupWaldhausenK0_reconciliation C a
  have hMap := rawToGroup_naturality C F 0 a
  exact (congrArg (fun x => groupWaldhausenK0Equiv D (groupMap C F 0 x)) h).symm.trans
    ((congrArg (groupWaldhausenK0Equiv D) hMap).symm.trans
      (hD.trans
        ((congrArg Multiplicative.ofAdd (rawWaldhausenK0Equiv_naturality C F a)).trans
          (congrArg (fun x => Multiplicative.ofAdd (WaldhausenKTheory.K0.map F x))
            ((congrArg Multiplicative.toAdd hC).symm.trans
              (congrArg (fun x => Multiplicative.toAdd (groupWaldhausenK0Equiv C x)) h))))))

/-- Independent category worlds retain the complete original group/Waldhausen K-zero square. -/
theorem groupWaldhausenK0Equiv_naturality (g : groupCarrier C 0) :
    groupWaldhausenK0Equiv D (groupMap C F 0 g) =
      Multiplicative.ofAdd
        (WaldhausenKTheory.K0.map F (Multiplicative.toAdd (groupWaldhausenK0Equiv C g))) :=
  groupWaldhausenK0NaturalityComputed C F g

/-- The original Waldhausen dictionary square commutes as a whole homomorphism square. -/
theorem groupWaldhausenK0Equiv_map :
    letI := groupStructure C 0
    letI := groupStructure D 0
    letI : MulOne (groupCarrier C 0) := (groupStructure C 0).toMulOneClass.toMulOne
    letI : MulOne (groupCarrier D 0) := (groupStructure D 0).toMulOneClass.toMulOne
    let qC := @MulEquiv.toMonoidHom _ _ (groupStructure C 0).toMulOneClass
      inferInstance (groupWaldhausenK0Equiv C)
    let qD := @MulEquiv.toMonoidHom _ _ (groupStructure D 0).toMulOneClass
      inferInstance (groupWaldhausenK0Equiv D)
    qD.comp (groupMap C F 0) = (WaldhausenKTheory.K0.map F).toMultiplicative.comp qC := by
  letI := groupStructure C 0
  letI := groupStructure D 0
  letI : MulOne (groupCarrier C 0) := (groupStructure C 0).toMulOneClass.toMulOne
  letI : MulOne (groupCarrier D 0) := (groupStructure D 0).toMulOneClass.toMulOne
  apply MonoidHom.ext
  exact groupWaldhausenK0Equiv_naturality C F

private theorem groupExactK0NaturalityComputed (g : groupCarrier C 0) :
    groupExactK0Equiv D (Additive.ofMul (groupMap C F 0 g)) =
      AlgebraicKTheory.K0.map F (groupExactK0Equiv C (Additive.ofMul g)) := by
  let a := (rawToGroup C 0).symm g
  have h := (rawToGroup C 0).apply_symm_apply g
  have hD := rawGroupExactK0_reconciliation D (NQKSpaceFunctorKiMap F 0 a)
  have hC := rawGroupExactK0_reconciliation C a
  have hMap := rawToGroup_naturality C F 0 a
  exact (congrArg (fun x => groupExactK0Equiv D (Additive.ofMul (groupMap C F 0 x))) h).symm.trans
    ((congrArg (fun x => groupExactK0Equiv D (Additive.ofMul x)) hMap).symm.trans
      (hD.trans ((rawExactK0Equiv_naturality C F a).trans
        (congrArg (AlgebraicKTheory.K0.map F)
          (hC.symm.trans
            (congrArg (fun x => groupExactK0Equiv C (Additive.ofMul x)) h))))))

/-- Independent category worlds retain the whole group/exact K-zero naturality square. -/
theorem groupExactK0Equiv_naturality (g : groupCarrier C 0) :
    groupExactK0Equiv D (Additive.ofMul (groupMap C F 0 g)) =
      AlgebraicKTheory.K0.map F (groupExactK0Equiv C (Additive.ofMul g)) :=
  groupExactK0NaturalityComputed C F g

private theorem bqPositiveMulCommComputed (n : ℕ) (a b : bqCarrier C (n + 1)) :
    letI := bqGroupStructure C (n + 1)
    a * b = b * a := by
  letI := HomotopyGroup.commGroup
    (N := Fin (n + 2)) (X := NQReal C) (x := NQReal.basepoint C)
  exact mul_comm a b

private theorem groupMulCommComputed (n : ℕ) (a b : groupCarrier C n) :
    letI := groupStructure C n
    a * b = b * a := by
  letI := groupStructure C n
  cases n with
  | zero =>
      let e := groupWaldhausenK0Equiv C
      exact e.injective ((e.map_mul a b).trans ((mul_comm (e a) (e b)).trans
        (e.map_mul b a).symm))
  | succ n =>
      letI := bqGroupStructure C (n + 1)
      let e := bqShift C (n + 1)
      exact e.injective ((e.map_mul a b).trans
        ((bqPositiveMulCommComputed C n (e a) (e b)).trans (e.map_mul b a).symm))

/-- Every actual connective group is commutative, with its original group data retained. -/
def commGroupStructure (n : ℕ) : CommGroup (groupCarrier C n) :=
  { groupStructure C n with mul_comm := groupMulCommComputed C n }

private theorem commGroupStructureGroupComputed (n : ℕ) :
    (commGroupStructure C n).toGroup = groupStructure C n := rfl

/-- Commutativity adds no new multiplication, unit, inverse or other group data. -/
theorem commGroupStructure_toGroup (n : ℕ) :
    (commGroupStructure C n).toGroup = groupStructure C n :=
  commGroupStructureGroupComputed C n

/-- The additive connective convention uses the same actual source group carrier. -/
abbrev additiveCarrier (n : ℕ) := Additive (groupCarrier C n)

/-- The all-degree additive group laws use the same original multiplicative group data. -/
def additiveGroupStructure (n : ℕ) : AddCommGroup (additiveCarrier C n) := by
  letI := commGroupStructure C n
  infer_instance

private def additiveMapComputed (n : ℕ) :
    letI := additiveGroupStructure C n
    letI := additiveGroupStructure D n
    additiveCarrier C n →+ additiveCarrier D n := by
  letI := groupStructure C n
  letI := groupStructure D n
  letI := additiveGroupStructure C n
  letI := additiveGroupStructure D n
  exact {
    toFun := fun a => Additive.ofMul (groupMap C F n (Additive.toMul a))
    map_zero' := (groupMap C F n).map_one
    map_add' := fun a b => (groupMap C F n).map_mul (Additive.toMul a) (Additive.toMul b) }

/-- Every additive connective map is the same original exact-functor group map
in additive notation. -/
def additiveMap (n : ℕ) :
    letI := additiveGroupStructure C n
    letI := additiveGroupStructure D n
    additiveCarrier C n →+ additiveCarrier D n :=
  additiveMapComputed C F n

private theorem additiveMapValueComputed (n : ℕ) (a : additiveCarrier C n) :
    additiveMap C F n a = Additive.ofMul (groupMap C F n (Additive.toMul a)) := rfl

/-- Additive notation retains every original group-map value and chosen root. -/
theorem additiveMap_apply (n : ℕ) (a : additiveCarrier C n) :
    additiveMap C F n a = Additive.ofMul (groupMap C F n (Additive.toMul a)) :=
  additiveMapValueComputed C F n a

private def additiveZeroK0EquivComputed :
    letI := additiveGroupStructure C 0
    additiveCarrier C 0 ≃+ AlgebraicKTheory.K0 C :=
  groupExactK0Equiv C

/-- The additive degree-zero group is the canonical exact K-zero,
through both original dictionaries. -/
def additiveZeroK0Equiv :
    @AddEquiv (additiveCarrier C 0) (AlgebraicKTheory.K0 C)
      (additiveGroupStructure C 0).toAddZeroClass.toAddZero.toAdd inferInstance :=
  additiveZeroK0EquivComputed C

private theorem additiveZeroK0NaturalityComputed (a : additiveCarrier C 0) :
    additiveZeroK0Equiv D (additiveMap C F 0 a) =
      AlgebraicKTheory.K0.map F (additiveZeroK0Equiv C a) :=
  groupExactK0Equiv_naturality C F (Additive.toMul a)

/-- The additive zero dictionary commutes with every independently sized additive exact functor. -/
theorem additiveZeroK0Equiv_naturality (a : additiveCarrier C 0) :
    additiveZeroK0Equiv D (additiveMap C F 0 a) =
      AlgebraicKTheory.K0.map F (additiveZeroK0Equiv C a) :=
  additiveZeroK0NaturalityComputed C F a

/-- The canonical exact K-zero dictionary square commutes on the complete additive maps. -/
theorem additiveZeroK0Equiv_map :
    letI := additiveGroupStructure C 0
    letI := additiveGroupStructure D 0
    letI : AddZero (additiveCarrier C 0) := (additiveGroupStructure C 0).toAddZeroClass.toAddZero
    letI : AddZero (additiveCarrier D 0) := (additiveGroupStructure D 0).toAddZeroClass.toAddZero
    let qC := @AddEquiv.toAddMonoidHom _ _ (additiveGroupStructure C 0).toAddZeroClass
      inferInstance (additiveZeroK0Equiv C)
    let qD := @AddEquiv.toAddMonoidHom _ _ (additiveGroupStructure D 0).toAddZeroClass
      inferInstance (additiveZeroK0Equiv D)
    qD.comp (additiveMap C F 0) = (AlgebraicKTheory.K0.map F).comp qC := by
  letI := additiveGroupStructure C 0
  letI := additiveGroupStructure D 0
  letI : AddZero (additiveCarrier C 0) := (additiveGroupStructure C 0).toAddZeroClass.toAddZero
  letI : AddZero (additiveCarrier D 0) := (additiveGroupStructure D 0).toAddZeroClass.toAddZero
  apply AddMonoidHom.ext
  exact additiveZeroK0Equiv_naturality C F

private theorem originalRawZeroIdentityComputed (a : rawCarrier C 0) :
    NQKSpaceFunctorKiMap (𝟭 C) 0 a = a := by
  let e := HomotopyGroup.pi0EquivZerothHomotopy (X := NQKSpace C) (x := zeroLoop C)
  have hComponents (c : ZerothHomotopy (NQKSpace C)) :
      ZerothHomotopy.lift
        (fun gamma : NQKSpace C => ZerothHomotopy.mk (NQKSpaceFunctorMap (𝟭 C) gamma))
        (fun {_ _} p => ZerothHomotopy.sound
          (p.map (NQKSpaceFunctorMap (𝟭 C)).continuous)) c = c := by
    induction c using ZerothHomotopy.rec with
    | mk gamma => exact ZerothHomotopy.sound ((NQKSpaceFunctorIdHomotopy C).evalAt gamma)
  exact e.injective ((NQKSpaceFunctorKiMap_zero_components (𝟭 C) a).trans (hComponents (e a)))

private theorem originalRawPositiveIdentityComputed (n : ℕ) (a : rawCarrier C (n + 1)) :
    NQKSpaceFunctorKiMap (𝟭 C) (n + 1) a = a := by
  let e := HomotopyGroup.loopShiftMulEquiv n (NQReal C) (NQReal.basepoint C)
  have hRoot :
      ((NQRealFunctorWeaklyPointed (𝟭 C)).rootPath.cast
        (DFunLike.congr_fun (NQRealFunctorWeaklyPointed_id_hom C)
          (NQReal.basepoint C)).symm rfl).Homotopic (Path.refl (NQReal.basepoint C)) :=
    ⟨NQKSpaceFunctorIdRootHomotopy C⟩
  exact e.injective
    ((congrArg e (NQKSpaceFunctorKiMap_succ_eq_positive (𝟭 C) n a)).trans
      ((originalPositiveShift_naturality C (𝟭 C) n a).trans
        (rootedIdentityValue (n + 1) (NQRealFunctorWeaklyPointed (𝟭 C)).hom
          (NQRealFunctorWeaklyPointed (𝟭 C)).rootPath
          (NQRealFunctorWeaklyPointed_id_hom C) hRoot (e a))))

private theorem originalRawIdentityComputed (n : ℕ) (a : rawCarrier C n) :
    NQKSpaceFunctorKiMap (𝟭 C) n a = a := by
  cases n with
  | zero => exact originalRawZeroIdentityComputed C a
  | succ n => exact originalRawPositiveIdentityComputed C n a

/-- Every original raw degree preserves identity using its actual zero root and unit contraction. -/
theorem originalRawMap_id (n : ℕ) (a : rawCarrier C n) :
    NQKSpaceFunctorKiMap (𝟭 C) n a = a :=
  originalRawIdentityComputed C n a

private theorem groupMapIdentityValueComputed (n : ℕ) (g : groupCarrier C n) :
    groupMap C (𝟭 C) n g = g := by
  let a := (rawToGroup C n).symm g
  have h := (rawToGroup C n).apply_symm_apply g
  exact (congrArg (groupMap C (𝟭 C) n) h).symm.trans
    ((rawToGroup_naturality C (𝟭 C) n a).symm.trans
      ((congrArg (rawToGroup C n) (originalRawMap_id C n a)).trans h))

/-- The actual all-degree group maps preserve identity without replacing the identity zero path. -/
theorem groupMap_id (n : ℕ) :
    letI := groupStructure C n
    groupMap C (𝟭 C) n = MonoidHom.id (groupCarrier C n) := by
  letI := groupStructure C n
  apply MonoidHom.ext
  exact groupMapIdentityValueComputed C n

private theorem bqMapIdentityValueComputed (n : ℕ) (g : bqCarrier C n) :
    bqMap C (𝟭 C) n g = g := by
  letI := groupStructure C n
  letI := bqGroupStructure C n
  let e := bqShift C n
  let a := e.symm g
  have h := e.apply_symm_apply g
  exact (congrArg (bqMap C (𝟭 C) n) h).symm.trans
    ((bqShift_naturality C (𝟭 C) n a).symm.trans
      ((congrArg e (groupMapIdentityValueComputed C n a)).trans h))

/-- The next-BQ maps preserve identity at every degree with the same original roots. -/
theorem bqMap_id (n : ℕ) :
    letI := bqGroupStructure C n
    bqMap C (𝟭 C) n = MonoidHom.id (bqCarrier C n) := by
  letI := bqGroupStructure C n
  apply MonoidHom.ext
  exact bqMapIdentityValueComputed C n

/-- The additive convention preserves identity on every actual connective group. -/
theorem additiveMap_id (n : ℕ) :
    letI := additiveGroupStructure C n
    additiveMap C (𝟭 C) n = AddMonoidHom.id (additiveCarrier C n) := by
  letI := additiveGroupStructure C n
  apply AddMonoidHom.ext
  intro a
  exact congrArg Additive.ofMul (groupMapIdentityValueComputed C n (Additive.toMul a))

variable {E : Type uE} [Category.{vE} E] [Preadditive E]
  [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E]

private theorem groupMapCompositionValueComputed (G : D ⥤ E) [G.Additive] [G.IsExact]
    (n : ℕ) (g : groupCarrier C n) :
    groupMap C (F ⋙ G) n g = groupMap D G n (groupMap C F n g) := by
  let a := (rawToGroup C n).symm g
  have h := (rawToGroup C n).apply_symm_apply g
  exact (congrArg (groupMap C (F ⋙ G) n) h).symm.trans
    ((rawToGroup_naturality C (F ⋙ G) n a).symm.trans
      ((congrArg (rawToGroup E n)
        (NQKSpaceFunctorKiMap_allIndices_original_comp F G n a)).trans
          ((rawToGroup_naturality D G n (NQKSpaceFunctorKiMap F n a)).trans
            ((congrArg (groupMap D G n) (rawToGroup_naturality C F n a)).trans
              (congrArg (fun x => groupMap D G n (groupMap C F n x)) h)))))

/-- All-degree connective group maps preserve composition in independent category worlds. -/
theorem groupMap_comp (G : D ⥤ E) [G.Additive] [G.IsExact] (n : ℕ) :
    letI := groupStructure C n
    letI := groupStructure D n
    letI := groupStructure E n
    letI : MulOne (groupCarrier C n) := (groupStructure C n).toMulOneClass.toMulOne
    letI : MulOne (groupCarrier D n) := (groupStructure D n).toMulOneClass.toMulOne
    letI : MulOne (groupCarrier E n) := (groupStructure E n).toMulOneClass.toMulOne
    groupMap C (F ⋙ G) n = (groupMap D G n).comp (groupMap C F n) := by
  letI := groupStructure C n
  letI := groupStructure D n
  letI := groupStructure E n
  letI : MulOne (groupCarrier C n) := (groupStructure C n).toMulOneClass.toMulOne
  letI : MulOne (groupCarrier D n) := (groupStructure D n).toMulOneClass.toMulOne
  letI : MulOne (groupCarrier E n) := (groupStructure E n).toMulOneClass.toMulOne
  apply MonoidHom.ext
  exact groupMapCompositionValueComputed C F G n

private theorem bqMapCompositionValueComputed (G : D ⥤ E) [G.Additive] [G.IsExact]
    (n : ℕ) (g : bqCarrier C n) :
    bqMap C (F ⋙ G) n g = bqMap D G n (bqMap C F n g) := by
  letI := groupStructure C n
  letI := groupStructure D n
  letI := groupStructure E n
  letI := bqGroupStructure C n
  letI := bqGroupStructure D n
  letI := bqGroupStructure E n
  let e := bqShift C n
  let a := e.symm g
  have h := e.apply_symm_apply g
  exact (congrArg (bqMap C (F ⋙ G) n) h).symm.trans
    ((bqShift_naturality C (F ⋙ G) n a).symm.trans
      ((congrArg (bqShift E n) (groupMapCompositionValueComputed C F G n a)).trans
        ((bqShift_naturality D G n (groupMap C F n a)).trans
          ((congrArg (bqMap D G n) (bqShift_naturality C F n a)).trans
            (congrArg (fun x => bqMap D G n (bqMap C F n x)) h)))))

/-- Every next-BQ homomorphism preserves actual composition with its original zero root. -/
theorem bqMap_comp (G : D ⥤ E) [G.Additive] [G.IsExact] (n : ℕ) :
    letI := bqGroupStructure C n
    letI := bqGroupStructure D n
    letI := bqGroupStructure E n
    letI : MulOne (bqCarrier C n) := (bqGroupStructure C n).toMulOneClass.toMulOne
    letI : MulOne (bqCarrier D n) := (bqGroupStructure D n).toMulOneClass.toMulOne
    letI : MulOne (bqCarrier E n) := (bqGroupStructure E n).toMulOneClass.toMulOne
    bqMap C (F ⋙ G) n = (bqMap D G n).comp (bqMap C F n) := by
  letI := bqGroupStructure C n
  letI := bqGroupStructure D n
  letI := bqGroupStructure E n
  letI : MulOne (bqCarrier C n) := (bqGroupStructure C n).toMulOneClass.toMulOne
  letI : MulOne (bqCarrier D n) := (bqGroupStructure D n).toMulOneClass.toMulOne
  letI : MulOne (bqCarrier E n) := (bqGroupStructure E n).toMulOneClass.toMulOne
  apply MonoidHom.ext
  exact bqMapCompositionValueComputed C F G n

/-- The additive connective maps preserve the same original composition in every degree. -/
theorem additiveMap_comp (G : D ⥤ E) [G.Additive] [G.IsExact] (n : ℕ) :
    letI := additiveGroupStructure C n
    letI := additiveGroupStructure D n
    letI := additiveGroupStructure E n
    letI : AddZero (additiveCarrier C n) := (additiveGroupStructure C n).toAddZeroClass.toAddZero
    letI : AddZero (additiveCarrier D n) := (additiveGroupStructure D n).toAddZeroClass.toAddZero
    letI : AddZero (additiveCarrier E n) := (additiveGroupStructure E n).toAddZeroClass.toAddZero
    additiveMap C (F ⋙ G) n = (additiveMap D G n).comp (additiveMap C F n) := by
  letI := additiveGroupStructure C n
  letI := additiveGroupStructure D n
  letI := additiveGroupStructure E n
  letI : AddZero (additiveCarrier C n) := (additiveGroupStructure C n).toAddZeroClass.toAddZero
  letI : AddZero (additiveCarrier D n) := (additiveGroupStructure D n).toAddZeroClass.toAddZero
  letI : AddZero (additiveCarrier E n) := (additiveGroupStructure E n).toAddZeroClass.toAddZero
  apply AddMonoidHom.ext
  intro a
  exact congrArg Additive.ofMul (groupMapCompositionValueComputed C F G n (Additive.toMul a))

private theorem groupMapNatIsoValueComputed (G : C ⥤ D) [G.Additive] [G.IsExact]
    (e : F ≅ G) (n : ℕ) (g : groupCarrier C n) :
    groupMap C F n g = groupMap C G n g := by
  let a := (rawToGroup C n).symm g
  have h := (rawToGroup C n).apply_symm_apply g
  exact (congrArg (groupMap C F n) h).symm.trans
    ((rawToGroup_naturality C F n a).symm.trans
      ((congrArg (rawToGroup D n)
        (NQKSpaceFunctorKiMap_allIndices_original_natIso F G e n a)).trans
          ((rawToGroup_naturality C G n a).trans (congrArg (groupMap C G n) h))))

/-- An actual natural isomorphism equates the complete original connective homomorphisms. -/
theorem groupMap_natIso (G : C ⥤ D) [G.Additive] [G.IsExact] (e : F ≅ G) (n : ℕ) :
    letI := groupStructure C n
    letI := groupStructure D n
    groupMap C F n = groupMap C G n := by
  letI := groupStructure C n
  letI := groupStructure D n
  apply MonoidHom.ext
  exact groupMapNatIsoValueComputed C F G e n

private theorem bqMapNatIsoValueComputed (G : C ⥤ D) [G.Additive] [G.IsExact]
    (e : F ≅ G) (n : ℕ) (g : bqCarrier C n) :
    bqMap C F n g = bqMap C G n g := by
  letI := groupStructure C n
  letI := groupStructure D n
  letI := bqGroupStructure C n
  letI := bqGroupStructure D n
  let q := bqShift C n
  let a := q.symm g
  have h := q.apply_symm_apply g
  exact (congrArg (bqMap C F n) h).symm.trans
    ((bqShift_naturality C F n a).symm.trans
      ((congrArg (bqShift D n) (groupMapNatIsoValueComputed C F G e n a)).trans
        ((bqShift_naturality C G n a).trans (congrArg (bqMap C G n) h))))

/-- The whole next-BQ map follows the original natural-isomorphism family in every degree. -/
theorem bqMap_natIso (G : C ⥤ D) [G.Additive] [G.IsExact] (e : F ≅ G) (n : ℕ) :
    letI := bqGroupStructure C n
    letI := bqGroupStructure D n
    bqMap C F n = bqMap C G n := by
  letI := bqGroupStructure C n
  letI := bqGroupStructure D n
  apply MonoidHom.ext
  exact bqMapNatIsoValueComputed C F G e n

/-- Additive notation retains the complete original natural-isomorphism transport. -/
theorem additiveMap_natIso (G : C ⥤ D) [G.Additive] [G.IsExact] (e : F ≅ G) (n : ℕ) :
    letI := additiveGroupStructure C n
    letI := additiveGroupStructure D n
    additiveMap C F n = additiveMap C G n := by
  letI := additiveGroupStructure C n
  letI := additiveGroupStructure D n
  apply AddMonoidHom.ext
  intro a
  exact congrArg Additive.ofMul (groupMapNatIsoValueComputed C F G e n (Additive.toMul a))

section PublicReadouts

private theorem bqGroupStructureZeroReadoutComputed :
    bqGroupStructure C 0 =
      (inferInstance : Group (FundamentalGroup (NQReal C) (NQReal.basepoint C))) := rfl

/-- The BQ degree-zero convention retains the original fundamental-group laws. -/
theorem bqGroupStructure_zero_value :
    bqGroupStructure C 0 =
      (inferInstance : Group (FundamentalGroup (NQReal C) (NQReal.basepoint C))) :=
  bqGroupStructureZeroReadoutComputed C

private theorem bqGroupStructureSuccReadoutComputed (n : ℕ) :
    bqGroupStructure C (n + 1) =
      HomotopyGroup.group (X := NQReal C) (x := NQReal.basepoint C) (Fin (n + 2)) := rfl

/-- Every positive BQ convention retains the original stock cube-group laws. -/
theorem bqGroupStructure_succ_value (n : ℕ) :
    bqGroupStructure C (n + 1) =
      HomotopyGroup.group (X := NQReal C) (x := NQReal.basepoint C) (Fin (n + 2)) :=
  bqGroupStructureSuccReadoutComputed C n

private theorem bqShiftZeroReadoutComputed (g : groupCarrier C 0) :
    bqShift C 0 g = g := rfl

/-- The zero shift is the literal identity on the original fundamental-group class. -/
theorem bqShift_zero_apply (g : groupCarrier C 0) : bqShift C 0 g = g :=
  bqShiftZeroReadoutComputed C g

private theorem bqMapZeroReadoutComputed (g : bqCarrier C 0) :
    bqMap C F 0 g = basedFundamentalGroupMap (NQRealFunctorWeaklyPointed F).hom
      (NQRealFunctorWeaklyPointed F).rootPath g := rfl

/-- The BQ zero map keeps the actual realization map and the original chosen root. -/
theorem bqMap_zero_apply (g : bqCarrier C 0) :
    bqMap C F 0 g = basedFundamentalGroupMap (NQRealFunctorWeaklyPointed F).hom
      (NQRealFunctorWeaklyPointed F).rootPath g := bqMapZeroReadoutComputed C F g

private theorem bqMapSuccReadoutComputed (n : ℕ) (g : bqCarrier C (n + 1)) :
    bqMap C F (n + 1) g =
      TopCat.homotopyGroupBasepointChangeMulEquiv (n + 1) (TopCat.of (NQReal D))
        (NQRealFunctorWeaklyPointed F).rootPath
        (HomotopyGroup.map (NQRealFunctorWeaklyPointed F).hom g) := rfl

/-- Every positive BQ map retains the actual realization and its complete original root. -/
theorem bqMap_succ_apply (n : ℕ) (g : bqCarrier C (n + 1)) :
    bqMap C F (n + 1) g =
      TopCat.homotopyGroupBasepointChangeMulEquiv (n + 1) (TopCat.of (NQReal D))
        (NQRealFunctorWeaklyPointed F).rootPath
        (HomotopyGroup.map (NQRealFunctorWeaklyPointed F).hom g) :=
  bqMapSuccReadoutComputed C F n g

private theorem rawWaldhausenK0ReadoutComputed (a : rawCarrier C 0) :
    rawWaldhausenK0Equiv C a = NQKSpacePiZeroEquivK0 C
      (HomotopyGroup.pi0EquivZerothHomotopy (X := NQKSpace C) (x := zeroLoop C) a) := rfl

/-- The raw Waldhausen dictionary evaluates the original complete cube-zero class. -/
theorem rawWaldhausenK0Equiv_apply (a : rawCarrier C 0) :
    rawWaldhausenK0Equiv C a = NQKSpacePiZeroEquivK0 C
      (HomotopyGroup.pi0EquivZerothHomotopy (X := NQKSpace C) (x := zeroLoop C) a) :=
  rawWaldhausenK0ReadoutComputed C a

private theorem groupWaldhausenK0ReadoutComputed (g : groupCarrier C 0) :
    groupWaldhausenK0Equiv C g = NQRealizedFundamentalK0MulEquiv C g := rfl

/-- The source zero-group dictionary is the original realized fundamental K-zero map. -/
theorem groupWaldhausenK0Equiv_apply (g : groupCarrier C 0) :
    groupWaldhausenK0Equiv C g = NQRealizedFundamentalK0MulEquiv C g :=
  groupWaldhausenK0ReadoutComputed C g

private theorem groupExactK0ReadoutComputed (g : groupCarrier C 0) :
    groupExactK0Equiv C (Additive.ofMul g) =
      WaldhausenKTheory.K0.toExact C (Multiplicative.toAdd (groupWaldhausenK0Equiv C g)) := rfl

/-- The group exact-K-zero dictionary follows the same literal Waldhausen forward. -/
theorem groupExactK0Equiv_apply (g : groupCarrier C 0) :
    groupExactK0Equiv C (Additive.ofMul g) =
      WaldhausenKTheory.K0.toExact C (Multiplicative.toAdd (groupWaldhausenK0Equiv C g)) :=
  groupExactK0ReadoutComputed C g

private theorem additiveZeroK0ReadoutComputed (a : additiveCarrier C 0) :
    additiveZeroK0Equiv C a = groupExactK0Equiv C a := rfl

/-- Additive notation keeps the same original group-to-exact-K-zero function. -/
theorem additiveZeroK0Equiv_apply (a : additiveCarrier C 0) :
    additiveZeroK0Equiv C a = groupExactK0Equiv C a := additiveZeroK0ReadoutComputed C a

end PublicReadouts

end ExactCategories

end AlgebraicKTheory.ConnectiveKGroups
