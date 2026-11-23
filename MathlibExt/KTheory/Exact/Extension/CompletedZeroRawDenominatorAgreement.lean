/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.ZeroFiberLocalization
public import MathlibExt.KTheory.Exact.Extension.LocalizedFiber
public import MathlibExt.KTheory.Exact.Extension.StabilizedFunctorRawMap
public import MathlibExt.CategoryTheory.Monoidal.CoreRealizedTranslations

/-!
# Actual mapped zero-row raw denominator and stabilizer agreement

Both original completed-Core routes retain the actual mapped denominator
isomorphism and stabilizer. Public characteristic values and the original
raw Core/zero-row recipes give these equalities on every raw morphism.
No equality of localized arrows is inferred from this coordinate leaf.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalActionCategory
open CategoryTheory.CoreLocalizationComparison
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory ZeroObject

attribute [local instance] AlgebraicKTheory.ExtensionCategory.leftSumAction
attribute [local instance] AlgebraicKTheory.FixedTargetExtension.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction
attribute [local instance]
  CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBiproducts

universe uC vC uD vD

namespace AlgebraicKTheory.FixedTargetExtension

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [F.IsExact]

private theorem actualCompletedZeroSourceDenominator
    {a b : SInverse (Core C) (Core C)} (r : RawHom a b) :
    HEq (ExtensionCategory.stabilizedFunctorRawMap F
      (localizedRawMap (zeroLocalizedRawMap r))).hom.2
      (⟨(F.mapBiprod r.stabilizer.of a.of.2.of).symm ≪≫ F.mapIso r.hom.2.iso⟩ :
        (F.core.obj r.stabilizer ⊗ F.core.obj a.of.2) ⟶ F.core.obj b.of.2) := by
  let q := localizedRawMap (zeroLocalizedRawMap r)
  have h := (ExtensionCategory.stabilizedFunctorRawMap_components F q).2.2
  exact h.trans (by apply heq_of_eq; rfl)

omit [ExactCategory C] [F.IsExact] in
private theorem actualCompletedZeroTargetDenominator
    {a b : SInverse (Core C) (Core C)} (r : RawHom a b) :
    HEq (localizedRawMap (zeroLocalizedRawMap
      (fromPairRaw (SInverseS.mapRawHom F (toPairRaw r))))).hom.2
      (⟨(F.mapBiprod r.stabilizer.of a.of.2.of).symm ≪≫ F.mapIso r.hom.2.iso⟩ :
        (F.core.obj r.stabilizer ⊗ F.core.obj a.of.2) ⟶ F.core.obj b.of.2) := by
  let q := fromPairRaw (SInverseS.mapRawHom F (toPairRaw r))
  have hIso : (localizedRawMap (zeroLocalizedRawMap q)).hom.2.iso =
      (F.mapBiprod r.stabilizer.of a.of.2.of).symm ≪≫ F.mapIso r.hom.2.iso := by
    rw [localizedRawMap_denominator]
    change q.hom.2.iso = _
    rw [fromPairRaw_denominator]
    rfl
  apply heq_of_eq
  apply Core.hom_ext
  exact congrArg Iso.hom hIso

/-- Both ACTUAL original zero-row raw routes have the same mapped denominator coordinate. -/
public theorem completedZeroRaw_denominator_agreement
    {a b : SInverse (Core C) (Core C)} (r : RawHom a b) :
    HEq (ExtensionCategory.stabilizedFunctorRawMap F
      (localizedRawMap (zeroLocalizedRawMap r))).hom.2
      (localizedRawMap (zeroLocalizedRawMap
        (fromPairRaw (SInverseS.mapRawHom F (toPairRaw r))))).hom.2 :=
  (actualCompletedZeroSourceDenominator F r).trans
    (actualCompletedZeroTargetDenominator F r).symm

private theorem actualCompletedZeroSourceStabilizer
    {a b : SInverse (Core C) (Core C)} (r : RawHom a b) :
    (ExtensionCategory.stabilizedFunctorRawMap F
      (localizedRawMap (zeroLocalizedRawMap r))).stabilizer = F.core.obj r.stabilizer := by
  have h := (ExtensionCategory.stabilizedFunctorRawMap_components F
    (localizedRawMap (zeroLocalizedRawMap r))).1
  exact h.trans (by rfl)

omit [ExactCategory C] [F.IsExact] in
private theorem actualCompletedZeroTargetStabilizer
    {a b : SInverse (Core C) (Core C)} (r : RawHom a b) :
    (localizedRawMap (zeroLocalizedRawMap
      (fromPairRaw (SInverseS.mapRawHom F (toPairRaw r))))).stabilizer =
        F.core.obj r.stabilizer := by
  rw [localizedRawMap_stabilizer]
  rfl

/-- The two ACTUAL original raw routes retain one common original mapped Core stabilizer. -/
public theorem completedZeroRaw_stabilizer_values
    {a b : SInverse (Core C) (Core C)} (r : RawHom a b) :
    (ExtensionCategory.stabilizedFunctorRawMap F
      (localizedRawMap (zeroLocalizedRawMap r))).stabilizer = F.core.obj r.stabilizer ∧
    (localizedRawMap (zeroLocalizedRawMap
      (fromPairRaw (SInverseS.mapRawHom F (toPairRaw r))))).stabilizer =
        F.core.obj r.stabilizer :=
  ⟨actualCompletedZeroSourceStabilizer F r, actualCompletedZeroTargetStabilizer F r⟩

end AlgebraicKTheory.FixedTargetExtension

end
