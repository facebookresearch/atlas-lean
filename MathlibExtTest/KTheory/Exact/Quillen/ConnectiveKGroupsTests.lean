/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Quillen.ConnectiveKGroups
public import MathlibExt.KTheory.Exact.Quillen.KSpaceHomotopyGroups

/-!
# Independent-universe clients of the connective Quillen group API

The clients retain the original loop carriers, zero and positive shifts, both
canonical K-zero dictionaries, actual root paths, and functor laws with six
independent category object and morphism universe roles.
-/

public section
noncomputable section

open CategoryTheory Limits Topology
open CategoryTheory.ExactCategory
open scoped ContinuousMap unitInterval Topology.Homotopy

universe uC vC uD vD uE vE

namespace AlgebraicKTheory.ConnectiveKGroups.Tests

section ExactCategories

variable (C : Type uC) [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

private local instance connectiveWaldhausenClient : WaldhausenCategory C :=
  ExactCategory.waldhausenCategory C

/-- Degree zero reads the actual component/fundamental-group dictionary. -/
theorem rawZeroShift_client
    (a : rawCarrier C 0) :
    rawToBQ C 0 a =
      loopComponentsEquivFundamentalGroup (NQReal C) (NQReal.basepoint C)
        (HomotopyGroup.pi0EquivZerothHomotopy (X := NQKSpace C) (x := zeroLoop C) a) := by
  rw [rawToBQ_apply, bqShift_zero_apply, rawToGroup_zero_apply]

/-- Every positive raw class follows the literal original stock loop shift. -/
theorem rawPositiveShift_client (n : ℕ)
    (a : rawCarrier C (n + 1)) :
    rawToBQ C (n + 1) a =
      HomotopyGroup.loopShiftMulEquiv n (NQReal C) (NQReal.basepoint C) a := by
  rw [rawToBQ_apply, bqShift_succ_apply, rawToGroup_succ_apply]

/-- The inverse zero shift also retains the original fundamental-group class. -/
theorem zeroShiftInverse_client (a : bqCarrier C 0) :
    let e := (rawToGroup C 0).symm.trans (rawToBQ C 0)
    e.symm a = a := by
  let e := (rawToGroup C 0).symm.trans (rawToBQ C 0)
  have he (g : groupCarrier C 0) : e g = g := by
    change rawToBQ C 0 ((rawToGroup C 0).symm g) = g
    rw [rawToBQ_apply, bqShift_zero_apply]
    exact (rawToGroup C 0).apply_symm_apply g
  exact (he (e.symm a)).symm.trans (e.apply_symm_apply a)

/-- The actual positive inverse is an inverse of the unchanged stock shift. -/
theorem positiveShiftInverse_client (n : ℕ) (a : bqCarrier C (n + 1)) :
    let e := (rawToGroup C (n + 1)).symm.trans (rawToBQ C (n + 1))
    HomotopyGroup.loopShiftMulEquiv n (NQReal C) (NQReal.basepoint C)
      (e.symm a) = a := by
  let e := (rawToGroup C (n + 1)).symm.trans (rawToBQ C (n + 1))
  have he (g : groupCarrier C (n + 1)) : e g =
      HomotopyGroup.loopShiftMulEquiv n (NQReal C) (NQReal.basepoint C) g := by
    change rawToBQ C (n + 1) ((rawToGroup C (n + 1)).symm g) = _
    rw [rawToBQ_apply, (rawToGroup C (n + 1)).apply_symm_apply, bqShift_succ_apply]
  exact (he (e.symm a)).symm.trans (e.apply_symm_apply a)

/-- The raw exact-K-zero dictionary retains the original canonical forward. -/
theorem canonicalRawK0_client (a : rawCarrier C 0) :
    rawExactK0Equiv C a = WaldhausenKTheory.K0.toExact C
      (NQKSpacePiZeroEquivK0 C
        (HomotopyGroup.pi0EquivZerothHomotopy (X := NQKSpace C) (x := zeroLoop C) a)) := by
  rw [rawExactK0Equiv_apply, rawWaldhausenK0Equiv_apply]

/-- The group and additive conventions reconcile with the same full raw zero class. -/
theorem canonicalGroupK0_client (a : rawCarrier C 0) :
    groupWaldhausenK0Equiv C (rawToGroup C 0 a) =
        Multiplicative.ofAdd (rawWaldhausenK0Equiv C a) ∧
      additiveZeroK0Equiv C (Additive.ofMul (rawToGroup C 0 a)) = rawExactK0Equiv C a := by
  constructor
  · exact rawGroupWaldhausenK0_reconciliation C a
  · rw [additiveZeroK0Equiv_apply]
    exact rawGroupExactK0_reconciliation C a

/-- The exact zero-group function is the actual canonical Waldhausen-to-exact map. -/
theorem canonicalGroupK0Forward_client (g : groupCarrier C 0) :
    groupExactK0Equiv C (Additive.ofMul g) =
      WaldhausenKTheory.K0.toExact C
        (Multiplicative.toAdd (NQRealizedFundamentalK0MulEquiv C g)) := by
  rw [groupExactK0Equiv_apply, groupWaldhausenK0Equiv_apply]

variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
  (F : C ⥤ D) [F.Additive] [F.IsExact]

/-- The original exact-functor unit retains its actual complete root contraction. -/
theorem originalFunctorRoot_client :
    NQKSpaceFunctorKiUnitRootPath F =
      (ContinuousMap.WeaklyPointed.loopUnitRootPath (NQRealFunctorWeaklyPointed F)).cast
        (DFunLike.congr_fun (NQKSpaceFunctorMap_eq_loopMap F) (zeroLoop C)) rfl :=
  originalFunctorUnitPath C F

/-- The full raw/BQ map square retains four independent category universe roles. -/
theorem mixedRawBQMap_client (n : ℕ) :
    (fun a : rawCarrier C n => rawToBQ D n (NQKSpaceFunctorKiMap F n a)) =
      fun a => bqMap C F n (rawToBQ C n a) :=
  funext (rawToBQ_naturality C F n)

/-- The zero BQ map uses the original realization and chosen comparison path. -/
theorem mixedZeroBQMap_client (g : bqCarrier C 0) :
    bqMap C F 0 g = basedFundamentalGroupMap (NQRealFunctorWeaklyPointed F).hom
      (NQRealFunctorWeaklyPointed F).rootPath g :=
  bqMap_zero_apply C F g

/-- The positive BQ map uses the original root in every shifted degree. -/
theorem mixedPositiveBQMap_client (n : ℕ) (g : bqCarrier C (n + 1)) :
    bqMap C F (n + 1) g =
      TopCat.homotopyGroupBasepointChangeMulEquiv (n + 1) (TopCat.of (NQReal D))
        (NQRealFunctorWeaklyPointed F).rootPath
        (HomotopyGroup.map (NQRealFunctorWeaklyPointed F).hom g) :=
  bqMap_succ_apply C F n g

/-- Both canonical K-zero maps retain the same original mixed exact functor. -/
theorem mixedCanonicalK0_client (a : rawCarrier C 0) :
    rawWaldhausenK0Equiv D (NQKSpaceFunctorKiMap F 0 a) =
        WaldhausenKTheory.K0.map F (rawWaldhausenK0Equiv C a) ∧
      rawExactK0Equiv D (NQKSpaceFunctorKiMap F 0 a) =
        AlgebraicKTheory.K0.map F (rawExactK0Equiv C a) :=
  ⟨rawWaldhausenK0Equiv_naturality C F a, rawExactK0Equiv_naturality C F a⟩

/-- Natural isomorphisms retain equality of the complete original group maps. -/
theorem mixedNaturalIso_client (G : C ⥤ D) [G.Additive] [G.IsExact]
    (e : F ≅ G) (n : ℕ) :
    letI := groupStructure C n
    letI := groupStructure D n
    groupMap C F n = groupMap C G n :=
  groupMap_natIso C F G e n

variable {E : Type uE} [Category.{vE} E] [Preadditive E]
  [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E]

/-- Whole group-map composition retains all six original category universe roles. -/
theorem mixedGroupComposition_client (G : D ⥤ E) [G.Additive] [G.IsExact] (n : ℕ) :
    letI := groupStructure C n
    letI := groupStructure D n
    letI := groupStructure E n
    letI : MulOne (groupCarrier C n) := (groupStructure C n).toMulOneClass.toMulOne
    letI : MulOne (groupCarrier D n) := (groupStructure D n).toMulOneClass.toMulOne
    letI : MulOne (groupCarrier E n) := (groupStructure E n).toMulOneClass.toMulOne
    groupMap C (F ⋙ G) n = (groupMap D G n).comp (groupMap C F n) :=
  groupMap_comp C F G n

/-- Whole BQ-map composition retains the same six original category roles. -/
theorem mixedBQComposition_client (G : D ⥤ E) [G.Additive] [G.IsExact] (n : ℕ) :
    letI := bqGroupStructure C n
    letI := bqGroupStructure D n
    letI := bqGroupStructure E n
    letI : MulOne (bqCarrier C n) := (bqGroupStructure C n).toMulOneClass.toMulOne
    letI : MulOne (bqCarrier D n) := (bqGroupStructure D n).toMulOneClass.toMulOne
    letI : MulOne (bqCarrier E n) := (bqGroupStructure E n).toMulOneClass.toMulOne
    bqMap C (F ⋙ G) n = (bqMap D G n).comp (bqMap C F n) :=
  bqMap_comp C F G n

/-- Whole additive-map composition retains the original maps in additive notation. -/
theorem mixedAdditiveComposition_client (G : D ⥤ E) [G.Additive] [G.IsExact] (n : ℕ) :
    letI := additiveGroupStructure C n
    letI := additiveGroupStructure D n
    letI := additiveGroupStructure E n
    letI : AddZero (additiveCarrier C n) := (additiveGroupStructure C n).toAddZeroClass.toAddZero
    letI : AddZero (additiveCarrier D n) := (additiveGroupStructure D n).toAddZeroClass.toAddZero
    letI : AddZero (additiveCarrier E n) := (additiveGroupStructure E n).toAddZeroClass.toAddZero
    additiveMap C (F ⋙ G) n = (additiveMap D G n).comp (additiveMap C F n) :=
  additiveMap_comp C F G n

end ExactCategories

/-- The retained ring carrier consumes the canonical positive raw/BQ shift
with its original projective-module and ring universe convention. -/
theorem legacyRingPositiveShift_client (R : Type uC) [Ring R] (n : ℕ)
    (a : AlgebraicKTheory.NQKSpaceHomotopyGroup R (n + 1)) :
    rawToBQ (FGProjectiveCat.{uC} R) (n + 1) a =
      HomotopyGroup.loopShiftMulEquiv n (NQReal (FGProjectiveCat.{uC} R))
        (NQReal.basepoint (FGProjectiveCat.{uC} R)) a :=
  rawPositiveShift_client (FGProjectiveCat.{uC} R) n a

/-- The retained ring-zero carrier remains raw; its explicit canonical
conversion into the distinct group convention retains the exact K-zero map. -/
theorem legacyRingZero_client (R : Type uC) [Ring R]
    (a : AlgebraicKTheory.NQKSpaceHomotopyGroup R 0) :
    groupExactK0Equiv (FGProjectiveCat.{uC} R)
        (Additive.ofMul (rawToGroup (FGProjectiveCat.{uC} R) 0 a)) =
      rawExactK0Equiv (FGProjectiveCat.{uC} R) a :=
  rawGroupExactK0_reconciliation (FGProjectiveCat.{uC} R) a

end AlgebraicKTheory.ConnectiveKGroups.Tests
