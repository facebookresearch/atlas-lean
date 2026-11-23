/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.ZeroRowIdentityCoordinateIso

/-!
# Whole naturality of the original identity-coordinate zero-row image

Every original core Iso maps through F on the middle coordinate. Both
identity-coordinate source components remain identities. The original
extension middle-map criterion therefore proves the whole source
NaturalIso, without a componentwise expected square or comparison input.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe uC vC uD vD

namespace AlgebraicKTheory.FixedTargetExtension

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [F.IsExact]

private theorem originalIdentityCoordinateMiddleComp
    {A B Z : AlgebraicKTheory.ExtensionCategory D} (a : A ⟶ B) (b : B ⟶ Z) :
    (AlgebraicKTheory.ExtensionCategory.homNormalization (a ≫ b)).hom.2.hom =
      (AlgebraicKTheory.ExtensionCategory.homNormalization a).hom.2.hom ≫
        (AlgebraicKTheory.ExtensionCategory.homNormalization b).hom.2.hom :=
  congrArg (fun k : A.subdivisionObj ⟶ Z.subdivisionObj => k.hom.2.hom)
    (AlgebraicKTheory.ExtensionCategory.homNormalization_comp a b)

private def originalIdentityCoordinateNatIsoComputed :
    zeroRowFunctor (C := C) ⋙ givenRowFunctor (0 : C) ⋙
        AlgebraicKTheory.ExtensionCategory.mapFunctor F ≅
      F.core ⋙ zeroRowFunctor (C := D) ⋙ givenRowFunctor (0 : D) := by
  let ZC := zeroRowFunctor (C := C)
  let YC := givenRowFunctor (C := C) (0 : C)
  let G := AlgebraicKTheory.ExtensionCategory.mapFunctor F
  let ZD := zeroRowFunctor (C := D)
  let YD := givenRowFunctor (C := D) (0 : D)
  let L := ZC ⋙ YC ⋙ G
  let R := F.core ⋙ ZD ⋙ YD
  let c (A : Core C) : L.obj A ≅ R.obj A := zeroRowIdentityCoordinateIso F A
  have hLObj (A : Core C) : (L.obj A).row.X₂ = F.obj A.of := by
    have hz : ZC.obj A = zeroRow A := rfl
    have hGiven : YC.obj (ZC.obj A) = (zeroRow A).toExtension :=
      (givenRowFunctor_obj (ZC.obj A)).trans
        (congrArg (fun E : FixedTargetExtension C (0 : C) => E.toExtension) hz)
    have hMiddle : (YC.obj (ZC.obj A)).row.X₂ = A.of :=
      congrArg (fun E : AlgebraicKTheory.ExtensionCategory C => E.row.X₂) hGiven
    exact (AlgebraicKTheory.ExtensionCategory.mapFunctor_middle_obj F
      (YC.obj (ZC.obj A))).trans (congrArg F.obj hMiddle)
  have hRObj (A : Core C) : (R.obj A).row.X₂ = F.obj A.of := by
    have hd : ZD.obj (F.core.obj A) = zeroRow (F.core.obj A) := rfl
    have hGiven : YD.obj (ZD.obj (F.core.obj A)) = (zeroRow (F.core.obj A)).toExtension :=
      (givenRowFunctor_obj (ZD.obj (F.core.obj A))).trans
        (congrArg (fun E : FixedTargetExtension D (0 : D) => E.toExtension) hd)
    exact congrArg (fun E : AlgebraicKTheory.ExtensionCategory D => E.row.X₂) hGiven
  refine NatIso.ofComponents c ?_
  intro A B f
  have hSource :
      (AlgebraicKTheory.ExtensionCategory.homNormalization (YC.map (ZC.map f))).hom.2.hom =
        f.iso.hom := by
    have hz : (ZC.map f).b = f.iso := rfl
    exact (inclusion_map_beta (ZC.map f)).trans (congrArg Iso.hom hz)
  have hLeftMap :
      HEq (AlgebraicKTheory.ExtensionCategory.homNormalization (L.map f)).hom.2.hom
        (F.map f.iso.hom) :=
    (AlgebraicKTheory.ExtensionCategory.mapFunctor_middle_heq F (YC.map (ZC.map f))).trans
      (heq_of_eq (congrArg F.map hSource))
  have hTarget :
      (AlgebraicKTheory.ExtensionCategory.homNormalization
        (YD.map (ZD.map (F.core.map f)))).hom.2.hom =
        (F.core.map f).iso.hom := by
    have hz : (ZD.map (F.core.map f)).b = (F.core.map f).iso := rfl
    exact (inclusion_map_beta (ZD.map (F.core.map f))).trans (congrArg Iso.hom hz)
  have hCore : (F.core.map f).iso.hom = F.map f.iso.hom := rfl
  have hRightMap :
      HEq (AlgebraicKTheory.ExtensionCategory.homNormalization (R.map f)).hom.2.hom
        (F.map f.iso.hom) :=
    heq_of_eq (hTarget.trans hCore)
  have hLeft := heq_comp (hLObj A) (hLObj B) (hRObj B) hLeftMap
    (zeroRowIdentityCoordinateIso_middle_heq F B)
  have hRight := heq_comp (hLObj A) (hRObj A) (hRObj B)
    (zeroRowIdentityCoordinateIso_middle_heq F A) hRightMap
  have hActual :
      (AlgebraicKTheory.ExtensionCategory.homNormalization (L.map f ≫ (c B).hom)).hom.2.hom =
        (AlgebraicKTheory.ExtensionCategory.homNormalization ((c A).hom ≫ R.map f)).hom.2.hom :=
    eq_of_heq ((heq_of_eq (originalIdentityCoordinateMiddleComp (L.map f) (c B).hom)).trans
      (hLeft.trans ((heq_of_eq (Category.comp_id (F.map f.iso.hom))).trans
        ((heq_of_eq (Category.id_comp (F.map f.iso.hom))).symm.trans
          (hRight.symm.trans
            (heq_of_eq (originalIdentityCoordinateMiddleComp (c A).hom (R.map f)).symm))))))
  exact AlgebraicKTheory.ExtensionCategory.hom_ext_of_middle _ _ hActual

/-- The actual identity-coordinate zero-row source Iso is natural on every original core arrow. -/
public def zeroRowIdentityCoordinateNatIso :
    zeroRowFunctor (C := C) ⋙ givenRowFunctor (0 : C) ⋙
        AlgebraicKTheory.ExtensionCategory.mapFunctor F ≅
      F.core ⋙ zeroRowFunctor (C := D) ⋙ givenRowFunctor (0 : D) :=
  originalIdentityCoordinateNatIsoComputed F

end AlgebraicKTheory.FixedTargetExtension

end
