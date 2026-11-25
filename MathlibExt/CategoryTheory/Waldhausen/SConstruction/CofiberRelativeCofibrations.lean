/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.CategoryTheory.Waldhausen.CofiberCornerQuotient
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.CofiberLevelwise

/-!
# Genuine relative cofibrations of cofiber sequences

The original first arrow of a cofiber sequence defines a functor to the
existing cofibration-arrow category. Its genuine relative cofibration
property pulls back to the existing cofiber-sequence category. Composition
and isomorphism closure are inherited, and all three evaluation components
are cofibrations: the quotient component follows from the actual corner
pushout theorem.

No Waldhausen structure on cofiber sequences is assumed or installed here.
-/

public section

open CategoryTheory Limits

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

namespace CofiberSequenceCategory

/-- The original source-to-middle cofibration and the original first two
components of a row map, in the existing cofibration-arrow category. -/
def sourceMiddleArrow : CofiberSequenceCategory C ⥤ Waldhausen.CofibrationArrow C where
  obj S := MorphismProperty.Arrow.mk (S.obj.map' 0 1) S.property.1
  map φ := MorphismProperty.Arrow.homMk
    (φ.hom.app (0 : Fin 3)) (φ.hom.app (1 : Fin 3))
    (φ.hom.naturality (homOfLE (show (0 : Fin 3) ≤ 1 from by decide))).symm
  map_id S := by
    apply MorphismProperty.Arrow.Hom.ext <;> rfl
  map_comp φ ψ := by
    apply MorphismProperty.Arrow.Hom.ext <;> rfl

private theorem sourceMiddleArrow_source_aux :
    sourceMiddleArrow C ⋙ Waldhausen.cofibrationArrowForget C ⋙ Arrow.leftFunc =
      source C := by
  unfold sourceMiddleArrow
  apply Functor.hext
  · intro S
    change ComposableArrows.obj' S.obj 0 = (source C).obj S
    exact (source_obj C S).symm
  · intro S T φ
    apply heq_of_eq
    change φ.hom.app (0 : Fin 3) = (source C).map φ
    exact (source_map C φ).symm

/-- The left evaluation of the original cofibration arrow is the existing
source functor on cofiber sequences. -/
theorem sourceMiddleArrow_source :
    sourceMiddleArrow C ⋙ Waldhausen.cofibrationArrowForget C ⋙ Arrow.leftFunc =
      source C :=
  sourceMiddleArrow_source_aux C

private theorem sourceMiddleArrow_middle_aux :
    sourceMiddleArrow C ⋙ Waldhausen.cofibrationArrowForget C ⋙ Arrow.rightFunc =
      middle C := by
  unfold sourceMiddleArrow
  apply Functor.hext
  · intro S
    change ComposableArrows.obj' S.obj 1 = (middle C).obj S
    exact (middle_obj C S).symm
  · intro S T φ
    apply heq_of_eq
    change φ.hom.app (1 : Fin 3) = (middle C).map φ
    exact (middle_map C φ).symm

/-- The right evaluation of the original cofibration arrow is the existing
middle functor on cofiber sequences. -/
theorem sourceMiddleArrow_middle :
    sourceMiddleArrow C ⋙ Waldhausen.cofibrationArrowForget C ⋙ Arrow.rightFunc =
      middle C :=
  sourceMiddleArrow_middle_aux C

/-- Cofibrations of cofiber sequences retain the genuine pushout-corner
condition of the existing relative cofibration-arrow property. -/
def relativeCofibrations : MorphismProperty (CofiberSequenceCategory C) :=
  (Waldhausen.cofibrationArrowCofibrations C).inverseImage (sourceMiddleArrow C)

private theorem memRelativeCofibrations_iff {S T : CofiberSequenceCategory C}
    (φ : S ⟶ T) :
    relativeCofibrations C φ ↔
      Waldhausen.IsRelativeCofibration C ((sourceMiddleArrow C).map φ) :=
  Iff.rfl

/-- Membership is the actual relative cofibration of the first-arrow map. -/
theorem mem_relativeCofibrations_iff {S T : CofiberSequenceCategory C}
    (φ : S ⟶ T) :
    relativeCofibrations C φ ↔
      Waldhausen.IsRelativeCofibration C ((sourceMiddleArrow C).map φ) :=
  memRelativeCofibrations_iff C φ

private theorem memRelativeCofibrationsRaw_iff
    {S T : CofiberSequenceCategory C} (φ : S ⟶ T) :
    relativeCofibrations C φ ↔
      IsCofibration (φ.hom.app (0 : Fin 3)) ∧
        ∃ (P : C) (inB : S.obj.obj' 1 ⟶ P) (inA : T.obj.obj' 0 ⟶ P)
          (d : P ⟶ T.obj.obj' 1),
          IsPushout (S.obj.map' 0 1) (φ.hom.app (0 : Fin 3)) inB inA ∧
            inB ≫ d = φ.hom.app (1 : Fin 3) ∧
            inA ≫ d = T.obj.map' 0 1 ∧ IsCofibration d := by
  unfold relativeCofibrations sourceMiddleArrow
  rfl

/-- The genuine relative property retains the original raw source and
middle components and the actual pushout-corner map. -/
theorem mem_relativeCofibrations_raw_iff
    {S T : CofiberSequenceCategory C} (φ : S ⟶ T) :
    relativeCofibrations C φ ↔
      IsCofibration (φ.hom.app (0 : Fin 3)) ∧
        ∃ (P : C) (inB : S.obj.obj' 1 ⟶ P) (inA : T.obj.obj' 0 ⟶ P)
          (d : P ⟶ T.obj.obj' 1),
          IsPushout (S.obj.map' 0 1) (φ.hom.app (0 : Fin 3)) inB inA ∧
            inB ≫ d = φ.hom.app (1 : Fin 3) ∧
            inA ≫ d = T.obj.map' 0 1 ∧ IsCofibration d :=
  memRelativeCofibrationsRaw_iff C φ

private theorem relativeCofibrations_multiplicative_aux :
    (relativeCofibrations C).IsMultiplicative := by
  unfold relativeCofibrations
  infer_instance

/-- Genuine cofiber-sequence cofibrations contain identities and are
closed under composition, by inverse-image inheritance. -/
instance relativeCofibrationsIsMultiplicative :
    (relativeCofibrations C).IsMultiplicative :=
  relativeCofibrations_multiplicative_aux C

private theorem relativeCofibrations_respectsIso_aux :
    (relativeCofibrations C).RespectsIso := by
  unfold relativeCofibrations
  infer_instance

/-- Genuine cofiber-sequence cofibrations respect isomorphisms, by the
existing relative-arrow property and inverse-image inheritance. -/
instance relativeCofibrationsRespectsIso :
    (relativeCofibrations C).RespectsIso :=
  relativeCofibrations_respectsIso_aux C

private theorem relativeCofibrations_components_aux
    {S T : CofiberSequenceCategory C} (φ : S ⟶ T)
    (h : relativeCofibrations C φ) :
    IsCofibration ((source C).map φ) ∧
      IsCofibration ((middle C).map φ) ∧ IsCofibration ((quotient C).map φ) := by
  have hArrow := (memRelativeCofibrations_iff C φ).mp h
  have hSource := hArrow.1
  have hMiddle := hArrow.right C
  have hS : IsCofiberSequence ((sourceMiddleArrow C).obj S).hom (S.obj.map' 1 2) := by
    change IsCofiberSequence (S.obj.map' 0 1) (S.obj.map' 1 2)
    exact S.property
  have hT : IsCofiberSequence ((sourceMiddleArrow C).obj T).hom (T.obj.map' 1 2) := by
    change IsCofiberSequence (T.obj.map' 0 1) (T.obj.map' 1 2)
    exact T.property
  have hqc : S.obj.map' 1 2 ≫ φ.hom.app (2 : Fin 3) =
      ((sourceMiddleArrow C).map φ).right ≫ T.obj.map' 1 2 :=
    φ.hom.naturality (homOfLE (show (1 : Fin 3) ≤ 2 from by decide))
  have hQuotient := hArrow.quotient C hS hT hqc
  refine ⟨?_, ?_, ?_⟩
  · change IsCofibration (φ.hom.app (0 : Fin 3))
    change IsCofibration (φ.hom.app (0 : Fin 3)) at hSource
    exact hSource
  · change IsCofibration (φ.hom.app (1 : Fin 3))
    change IsCofibration (φ.hom.app (1 : Fin 3)) at hMiddle
    exact hMiddle
  · change IsCofibration (φ.hom.app (2 : Fin 3))
    exact hQuotient

/-- Every genuine relative cofiber-sequence cofibration is a cofibration
under each of the three existing evaluation functors. -/
theorem relativeCofibrations_components
    {S T : CofiberSequenceCategory C} (φ : S ⟶ T)
    (h : relativeCofibrations C φ) :
    IsCofibration ((source C).map φ) ∧
      IsCofibration ((middle C).map φ) ∧ IsCofibration ((quotient C).map φ) :=
  relativeCofibrations_components_aux C φ h

/-- Genuine relative cofibrations imply the existing levelwise
cofibration property, including the quotient condition. -/
theorem relativeCofibrations_le_levelwiseCofibrations :
    relativeCofibrations C ≤ levelwiseCofibrations C := by
  intro S T φ h
  exact (mem_levelwiseCofibrations_iff C φ).mpr
    (relativeCofibrations_components C φ h)

end CofiberSequenceCategory

end CategoryTheory.Waldhausen.SConstruction
