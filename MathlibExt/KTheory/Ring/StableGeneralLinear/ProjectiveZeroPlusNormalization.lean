/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.NativeProjectiveZeroPlusCalibration

/-!
# Joint native zero/plus normalization with explicit carrier data

The same original maps and complete family values are stored in a flat
record with explicit carrier types. A proof bundle retains every original
point, full relative condition, complete unit trace and both source triangles.
Typed accessors keep the original normalization interface and family values.
-/

noncomputable section

open CategoryTheory Topology
open CategoryTheory.SInverseS.ComponentTranslation
open scoped ContinuousMap

universe uA uB uZ uP uO uR uM uProbe

namespace AlgebraicKTheory.StableGL

/-- The complete endpoint and relative conditions of a specified
continuous family, with its SAME original continuous-map value. -/
public def normalizationRelativeFamilyConditions
    {X : Type uA} {Y : Type uB} [TopologicalSpace X] [TopologicalSpace Y]
    (F : C(unitInterval × X, Y)) (f g : C(X, Y)) (s : Set X) : Prop :=
  (∀ x, F (0, x) = f x) ∧ (∀ x, F (1, x) = g x) ∧
    ∀ t x, x ∈ s → F (t, x) = f x

private theorem normalizationRelativeFamilyConditions_of_rel
    {X : Type uA} {Y : Type uB} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} {s : Set X} (F : ContinuousMap.HomotopyRel f g s) :
    normalizationRelativeFamilyConditions F.toContinuousMap f g s :=
  ⟨F.map_zero_left, F.map_one_left, fun t _ hx => F.eq_fst t hx⟩

private def normalizationRelativeFamily_of_conditions
    {X : Type uA} {Y : Type uB} [TopologicalSpace X] [TopologicalSpace Y]
    (F : C(unitInterval × X, Y)) (f g : C(X, Y)) (s : Set X)
    (h : normalizationRelativeFamilyConditions F f g s) :
    ContinuousMap.HomotopyRel f g s where
  toContinuousMap := F
  map_zero_left := h.1
  map_one_left := h.2.1
  prop' := h.2.2

/-- All original maps and full family values with INDEPENDENT field
types. The five explicit carriers keep generated equality/size checks
independent of model/equivalence-field projections. -/
public structure NativeProjectiveZeroPlusMapData
    (A : Type uA) (B : Type uB) (Z : Type uZ) (P : Type uP) (O : Type uO)
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace Z]
    [TopologicalSpace P] [TopologicalSpace O] where
  /-- The ORIGINAL model-zero homotopy equivalence. -/
  model : A ≃ₕ B
  /-- The ENTIRE ORIGINAL model left inverse family value. -/
  modelLeft : C(unitInterval × A, A)
  /-- The ENTIRE ORIGINAL model right inverse family value. -/
  modelRight : C(unitInterval × B, B)
  /-- The ORIGINAL native-zero/independent-plus homotopy equivalence. -/
  equiv : Z ≃ₕ P
  /-- The ENTIRE ORIGINAL native left inverse family value. -/
  leftFamily : C(unitInterval × Z, Z)
  /-- The ENTIRE ORIGINAL independent-plus right inverse family value. -/
  rightFamily : C(unitInterval × P, P)
  /-- The SAME ORIGINAL prescribed BGL-to-native-zero source map. -/
  sourceMap : C(O, Z)
  /-- The ENTIRE ORIGINAL forward BGL-source triangle family value. -/
  sourceTriangle : C(unitInterval × O, P)

/-- The exact original carriers of the jointly chosen normalization. -/
public abbrev nativeProjectiveZeroPlusNormalizationData
    (R : Type uR) [Ring R] :=
  NativeProjectiveZeroPlusMapData
    (zeroSpace (C := FGProjectiveCat.IdempotentModel R))
    (zeroSpace (C := FGProjectiveCat.{max uR uM} R))
    (AlgebraicKTheory.RingK0.projectiveZeroSpace.{uR, uM, uProbe} R)
    (independentBGLCellTarget R) (ordinaryBGL R)

/-- Every original point, complete family condition, unit trace and
source equation, with no compatibility or inverse conclusion dropped. -/
public structure NativeProjectiveZeroPlusNormalizationLaws
    (R : Type uR) [Ring R]
    (d : nativeProjectiveZeroPlusNormalizationData.{uR, uM, uProbe} R) : Prop where
  /-- The ORIGINAL model forward point equation. -/
  modelPoint : d.model.toFun (zeroSpacePoint (C := FGProjectiveCat.IdempotentModel R)) =
    zeroSpacePoint (C := FGProjectiveCat.{max uR uM} R)
  /-- The ORIGINAL model inverse point equation. -/
  modelInversePoint : d.model.invFun (zeroSpacePoint (C := FGProjectiveCat.{max uR uM} R)) =
    zeroSpacePoint (C := FGProjectiveCat.IdempotentModel R)
  /-- BOTH endpoints and full point-relative condition of the ORIGINAL model left family. -/
  modelLeft : normalizationRelativeFamilyConditions d.modelLeft
    (d.model.invFun.comp d.model.toFun)
    (ContinuousMap.id (zeroSpace (C := FGProjectiveCat.IdempotentModel R)))
    {zeroSpacePoint (C := FGProjectiveCat.IdempotentModel R)}
  /-- BOTH endpoints and full point-relative condition of the ORIGINAL model right family. -/
  modelRight : normalizationRelativeFamilyConditions d.modelRight
    (d.model.toFun.comp d.model.invFun)
    (ContinuousMap.id (zeroSpace (C := FGProjectiveCat.{max uR uM} R)))
    {zeroSpacePoint (C := FGProjectiveCat.{max uR uM} R)}
  /-- The ENTIRE prescribed ORIGINAL model/unit retuning trace. -/
  modelTrace : ∃ K : ContinuousMap.Homotopy
      (finiteFreeRowProjectiveZeroHomotopyEquiv.{uR, uM} R).toFun d.model.toFun,
    ∀ t : unitInterval,
      K (t, zeroSpacePoint (C := FGProjectiveCat.IdempotentModel R)) =
        finiteFreeRowProjectiveZeroUnitPath.{uR, uM} R t
  /-- The ORIGINAL native-to-plus point equation. -/
  forwardPoint : d.equiv.toFun
    (AlgebraicKTheory.RingK0.projectiveZeroPoint.{uR, uM, uProbe} R) =
      independentBGLCellPoint R
  /-- The ORIGINAL plus-to-native point equation. -/
  backwardPoint : d.equiv.invFun (independentBGLCellPoint R) =
    AlgebraicKTheory.RingK0.projectiveZeroPoint.{uR, uM, uProbe} R
  /-- BOTH endpoints and full ORIGINAL native left-relative family condition. -/
  leftFamily : normalizationRelativeFamilyConditions d.leftFamily
    (d.equiv.invFun.comp d.equiv.toFun)
    (ContinuousMap.id (AlgebraicKTheory.RingK0.projectiveZeroSpace.{uR, uM, uProbe} R))
    {AlgebraicKTheory.RingK0.projectiveZeroPoint.{uR, uM, uProbe} R}
  /-- BOTH endpoints and full ORIGINAL plus right-relative family condition. -/
  rightFamily : normalizationRelativeFamilyConditions d.rightFamily
    (d.equiv.toFun.comp d.equiv.invFun)
    (ContinuousMap.id (independentBGLCellTarget R)) {independentBGLCellPoint R}
  /-- The SAME ORIGINAL model/native source-map formula. -/
  sourceFormula : d.sourceMap =
    (nativeZeroRealizationIso.{(max uR uM) + 1, max uR uM, uProbe}
      (C := FGProjectiveCat.{max uR uM} R)).inv.hom.comp
        (d.model.toFun.comp (finiteFreeRowBasedZeroComparison R).hom)
  /-- The ORIGINAL prescribed BGL-source point equation. -/
  sourcePoint : d.sourceMap (ordinaryBGLBasepoint R) =
    AlgebraicKTheory.RingK0.projectiveZeroPoint.{uR, uM, uProbe} R
  /-- The STRICT ORIGINAL inverse BGL-source triangle. -/
  inverseSourceTriangle : d.equiv.invFun.comp (independentBGLCellInclusion R).hom = d.sourceMap
  /-- BOTH endpoints and complete ORIGINAL BGL-point-relative forward triangle. -/
  sourceTriangle : normalizationRelativeFamilyConditions d.sourceTriangle
    (d.equiv.toFun.comp d.sourceMap) (independentBGLCellInclusion R).hom
    {ordinaryBGLBasepoint R}

/-- The ORIGINAL joint normalization, with independent map/family data
and every original dependent condition preserved in its proof bundle. -/
public structure NativeProjectiveZeroPlusNormalization (R : Type uR) [Ring R] where
  /-- All SAME original maps and complete family continuous values. -/
  data : nativeProjectiveZeroPlusNormalizationData.{uR, uM, uProbe} R
  /-- All SAME original points, relative conditions, unit trace and source triangles. -/
  valid : NativeProjectiveZeroPlusNormalizationLaws.{uR, uM, uProbe} R data

namespace NativeProjectiveZeroPlusNormalization

variable {R : Type uR} [Ring R]
  (N : NativeProjectiveZeroPlusNormalization.{uR, uM, uProbe} R)

/-- The SAME ORIGINAL model homotopy equivalence. -/
public def model :
    zeroSpace (C := FGProjectiveCat.IdempotentModel R) ≃ₕ
      zeroSpace (C := FGProjectiveCat.{max uR uM} R) :=
  N.data.model

/-- The ORIGINAL model forward point equation. -/
public theorem modelPoint :
    N.model.toFun (zeroSpacePoint (C := FGProjectiveCat.IdempotentModel R)) =
      zeroSpacePoint (C := FGProjectiveCat.{max uR uM} R) :=
  N.valid.modelPoint

/-- The ORIGINAL model inverse point equation. -/
public theorem modelInversePoint :
    N.model.invFun (zeroSpacePoint (C := FGProjectiveCat.{max uR uM} R)) =
      zeroSpacePoint (C := FGProjectiveCat.IdempotentModel R) :=
  N.valid.modelInversePoint

/-- The ENTIRE SAME ORIGINAL model left inverse family, with its original relative locus. -/
public def modelLeft :
    ContinuousMap.HomotopyRel (N.model.invFun.comp N.model.toFun)
      (ContinuousMap.id (zeroSpace (C := FGProjectiveCat.IdempotentModel R)))
      {zeroSpacePoint (C := FGProjectiveCat.IdempotentModel R)} :=
  normalizationRelativeFamily_of_conditions N.data.modelLeft _ _ _ N.valid.modelLeft

/-- The ENTIRE SAME ORIGINAL model right inverse family, with its original relative locus. -/
public def modelRight :
    ContinuousMap.HomotopyRel (N.model.toFun.comp N.model.invFun)
      (ContinuousMap.id (zeroSpace (C := FGProjectiveCat.{max uR uM} R)))
      {zeroSpacePoint (C := FGProjectiveCat.{max uR uM} R)} :=
  normalizationRelativeFamily_of_conditions N.data.modelRight _ _ _ N.valid.modelRight

/-- The ENTIRE prescribed ORIGINAL model/unit retuning trace. -/
public theorem modelTrace : ∃ K : ContinuousMap.Homotopy
      (finiteFreeRowProjectiveZeroHomotopyEquiv.{uR, uM} R).toFun N.model.toFun,
    ∀ t : unitInterval,
      K (t, zeroSpacePoint (C := FGProjectiveCat.IdempotentModel R)) =
        finiteFreeRowProjectiveZeroUnitPath.{uR, uM} R t :=
  N.valid.modelTrace

/-- The SAME ORIGINAL native-zero/independent-plus equivalence. -/
public def equiv :
    AlgebraicKTheory.RingK0.projectiveZeroSpace.{uR, uM, uProbe} R ≃ₕ
      independentBGLCellTarget R :=
  N.data.equiv

/-- The ORIGINAL native-to-plus point equation. -/
public theorem forwardPoint :
    N.equiv.toFun (AlgebraicKTheory.RingK0.projectiveZeroPoint.{uR, uM, uProbe} R) =
      independentBGLCellPoint R :=
  N.valid.forwardPoint

/-- The ORIGINAL plus-to-native point equation. -/
public theorem backwardPoint :
    N.equiv.invFun (independentBGLCellPoint R) =
      AlgebraicKTheory.RingK0.projectiveZeroPoint.{uR, uM, uProbe} R :=
  N.valid.backwardPoint

/-- The ENTIRE SAME ORIGINAL native left inverse family. -/
public def leftFamily :
    ContinuousMap.HomotopyRel (N.equiv.invFun.comp N.equiv.toFun)
      (ContinuousMap.id (AlgebraicKTheory.RingK0.projectiveZeroSpace.{uR, uM, uProbe} R))
      {AlgebraicKTheory.RingK0.projectiveZeroPoint.{uR, uM, uProbe} R} :=
  normalizationRelativeFamily_of_conditions N.data.leftFamily _ _ _ N.valid.leftFamily

/-- The ENTIRE SAME ORIGINAL independent-plus right inverse family. -/
public def rightFamily :
    ContinuousMap.HomotopyRel (N.equiv.toFun.comp N.equiv.invFun)
      (ContinuousMap.id (independentBGLCellTarget R)) {independentBGLCellPoint R} :=
  normalizationRelativeFamily_of_conditions N.data.rightFamily _ _ _ N.valid.rightFamily

/-- The SAME ORIGINAL prescribed BGL-to-native source map. -/
public def sourceMap :
    C(ordinaryBGL R, AlgebraicKTheory.RingK0.projectiveZeroSpace.{uR, uM, uProbe} R) :=
  N.data.sourceMap

/-- The SAME ORIGINAL source formula, including the native realization Iso. -/
public theorem sourceFormula : N.sourceMap =
    (nativeZeroRealizationIso.{(max uR uM) + 1, max uR uM, uProbe}
      (C := FGProjectiveCat.{max uR uM} R)).inv.hom.comp
        (N.model.toFun.comp (finiteFreeRowBasedZeroComparison R).hom) :=
  N.valid.sourceFormula

/-- The ORIGINAL prescribed BGL-source point equation. -/
public theorem sourcePoint : N.sourceMap (ordinaryBGLBasepoint R) =
    AlgebraicKTheory.RingK0.projectiveZeroPoint.{uR, uM, uProbe} R :=
  N.valid.sourcePoint

/-- The STRICT SAME ORIGINAL inverse BGL-source triangle. -/
public theorem inverseSourceTriangle :
    N.equiv.invFun.comp (independentBGLCellInclusion R).hom = N.sourceMap :=
  N.valid.inverseSourceTriangle

/-- The ENTIRE SAME ORIGINAL forward BGL-source triangle relative to the original BGL point. -/
public def sourceTriangle :
    ContinuousMap.HomotopyRel (N.equiv.toFun.comp N.sourceMap)
      (independentBGLCellInclusion R).hom {ordinaryBGLBasepoint R} :=
  normalizationRelativeFamily_of_conditions N.data.sourceTriangle _ _ _ N.valid.sourceTriangle

/-- ALL five exported complete relative families have LITERALLY the
stored ORIGINAL continuous-map values, with every source point/time retained. -/
public theorem fullFamilyValues :
    N.modelLeft.toContinuousMap = N.data.modelLeft ∧
      N.modelRight.toContinuousMap = N.data.modelRight ∧
      N.leftFamily.toContinuousMap = N.data.leftFamily ∧
      N.rightFamily.toContinuousMap = N.data.rightFamily ∧
      N.sourceTriangle.toContinuousMap = N.data.sourceTriangle :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

end NativeProjectiveZeroPlusNormalization

/-- The same joint source-bearing producer constructs every ORIGINAL
map, full family, point, unit trace and source condition from the Ring alone. -/
public theorem nativeProjectiveZeroPlusNormalization_nonempty
    (R : Type uR) [Ring R] :
    Nonempty (NativeProjectiveZeroPlusNormalization.{uR, uM, uProbe} R) := by
  let Z := AlgebraicKTheory.RingK0.projectiveZeroSpace.{uR, uM, uProbe} R
  let z := AlgebraicKTheory.RingK0.projectiveZeroPoint.{uR, uM, uProbe} R
  obtain ⟨d, hd, hdi, ⟨DL⟩, ⟨DR⟩, hTrace,
    a, ha, hai, ⟨L⟩, ⟨A⟩, hInverse, ⟨T⟩⟩ :=
    nativeProjectiveZeroPlusCalibratedEquivalence_exists.{uR, uM, uProbe} R
  let q : C(ordinaryBGL R, Z) :=
    (nativeZeroRealizationIso.{(max uR uM) + 1, max uR uM, uProbe}
      (C := FGProjectiveCat.{max uR uM} R)).inv.hom.comp
        (d.toFun.comp (finiteFreeRowBasedZeroComparison R).hom)
  have hInverseSource : a.invFun.comp (independentBGLCellInclusion R).hom = q := hInverse
  have hq : q (ordinaryBGLBasepoint R) = z := by
    calc
      q (ordinaryBGLBasepoint R) = a.invFun
          (independentBGLCellInclusion R (ordinaryBGLBasepoint R)) :=
        (congrArg (fun f : C(ordinaryBGL R, Z) => f (ordinaryBGLBasepoint R))
          hInverseSource).symm
      _ = a.invFun (independentBGLCellPoint R) :=
        congrArg a.invFun (independentBGLCellInclusion_point R)
      _ = z := hai
  let D : nativeProjectiveZeroPlusNormalizationData.{uR, uM, uProbe} R :=
    { model := d
      modelLeft := DL.toContinuousMap
      modelRight := DR.toContinuousMap
      equiv := a
      leftFamily := L.toContinuousMap
      rightFamily := A.toContinuousMap
      sourceMap := q
      sourceTriangle := T.toContinuousMap }
  have hD : NativeProjectiveZeroPlusNormalizationLaws.{uR, uM, uProbe} R D :=
    { modelPoint := hd
      modelInversePoint := hdi
      modelLeft := normalizationRelativeFamilyConditions_of_rel DL
      modelRight := normalizationRelativeFamilyConditions_of_rel DR
      modelTrace := hTrace
      forwardPoint := ha
      backwardPoint := hai
      leftFamily := normalizationRelativeFamilyConditions_of_rel L
      rightFamily := normalizationRelativeFamilyConditions_of_rel A
      sourceFormula := rfl
      sourcePoint := hq
      inverseSourceTriangle := hInverseSource
      sourceTriangle := normalizationRelativeFamilyConditions_of_rel T }
  exact ⟨{ data := D, valid := hD }⟩

/-- Select the SAME jointly normalized original maps, complete unit trace,
BOTH model/native relative families and BOTH original source triangles. -/
public def nativeProjectiveZeroPlusNormalizationOfRing
    (R : Type uR) [Ring R] :
    NativeProjectiveZeroPlusNormalization.{uR, uM, uProbe} R :=
  Classical.choice (nativeProjectiveZeroPlusNormalization_nonempty.{uR, uM, uProbe} R)

end AlgebraicKTheory.StableGL

end
