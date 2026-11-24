/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.CofiberEvaluation
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.CofiberExactFunctor
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageTwoFunctor
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageFunctoriality

/-!
# Evaluation and stage-two naturality for exact functors

For an additive exact functor `F : C ⥤ D` between Quillen exact categories
over independent universes, evaluation after the cofiber lift agrees with
postcomposition after evaluation: source and quotient naturality, and
stage-two-functor naturality through `mapStage`.

Orientation: the lifted-then-evaluated composite is on the left,
`cofiberSequenceFunctor F ⋙ source D`, `cofiberSequenceFunctor F ⋙ quotient D`,
and `cofiberSequenceFunctor F ⋙ stageTwoFunctor D`; the
evaluated-then-mapped composite is on the right, `source C ⋙ F`,
`quotient C ⋙ F`, and `stageTwoFunctor C ⋙ mapStage C D F 2`.
This orientation is used consistently for all three isomorphisms.

Reuse map: `CofiberSequenceCategory.source` and `quotient` with their
object and map computation laws, `cofiberSequenceFunctor F` with
`F.mapComposableArrows`, `stageTwoFunctor` with its object and map
computation laws, `mapStage` with its object and map computation laws,
`NatIso.ofComponents`, `eqToIso`, and ordinary category laws.
No biproduct-preservation API is used.

Explicit nonclaims: no paired source-quotient naturality, no split-section
naturality, no split-section-stage naturality, no nerve, no realization,
no additivity equivalence, no K-space, no `π₀`, no spectra, and no Q/S
comparison.
-/

@[expose] public section

open CategoryTheory Limits ZeroObject

universe v₁ u₁ v₂ u₂

namespace CategoryTheory.Waldhausen.SConstruction

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type u₂} [Category.{v₂} D] [Preadditive D] [HasZeroObject D]
  [HasBinaryBiproducts D] [ExactCategory D]

/-- The Waldhausen category structure on `C` from its exact structure, as a local instance. -/
local instance cofiberEvaluationNaturalityWaldhausenC : WaldhausenCategoryWithoutGluing C :=
    ExactCategory.waldhausenCategory C
/-- The Waldhausen category structure on `D` from its exact structure, as a local instance. -/
local instance cofiberEvaluationNaturalityWaldhausenD : WaldhausenCategoryWithoutGluing D :=
    ExactCategory.waldhausenCategory D

variable (F : C ⥤ D) [F.Additive] [F.IsExact]

/-- Source naturality: evaluating after the cofiber lift agrees with
postcomposition after source evaluation. -/
noncomputable def sourceNaturalityIso :
    cofiberSequenceFunctor F ⋙ CofiberSequenceCategory.source D ≅
      CofiberSequenceCategory.source C ⋙ F :=
  NatIso.ofComponents (fun S => eqToIso (by rfl)) (fun {S T} φ => by
    -- Exact `mapComposableArrows`/evaluation computation via
    -- `CofiberSequenceCategory.source_map` and lift/whisker `rfl`s;
    -- both `eqToIso` homs are `𝟙` by `rfl`.
    change F.map (φ.hom.app 0) ≫ 𝟙 _ = 𝟙 _ ≫ F.map (φ.hom.app 0)
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- Quotient naturality: evaluating after the cofiber lift agrees with
postcomposition after quotient evaluation. -/
noncomputable def quotientNaturalityIso :
    cofiberSequenceFunctor F ⋙ CofiberSequenceCategory.quotient D ≅
      CofiberSequenceCategory.quotient C ⋙ F :=
  NatIso.ofComponents (fun S => eqToIso (by rfl)) (fun {S T} φ => by
    -- Exact `mapComposableArrows`/evaluation computation via
    -- `CofiberSequenceCategory.quotient_map` and lift/whisker `rfl`s;
    -- both `eqToIso` homs are `𝟙` by `rfl`.
    change F.map (φ.hom.app 2) ≫ 𝟙 _ = 𝟙 _ ≫ F.map (φ.hom.app 2)
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- Source component computes as the identity. -/
@[simp]
theorem sourceNaturalityIso_hom_app (S : CofiberSequenceCategory C) :
    (sourceNaturalityIso F).hom.app S = 𝟙 _ := by
  have h : (sourceNaturalityIso F).hom.app S =
      (eqToIso (rfl : ((cofiberSequenceFunctor F ⋙ CofiberSequenceCategory.source D).obj S =
        ((CofiberSequenceCategory.source C ⋙ F).obj S)))).hom := rfl
  rw [h]
  rfl

/-- Quotient component computes as the identity. -/
@[simp]
theorem quotientNaturalityIso_hom_app (S : CofiberSequenceCategory C) :
    (quotientNaturalityIso F).hom.app S = 𝟙 _ := by
  have h : (quotientNaturalityIso F).hom.app S =
      (eqToIso (rfl : ((cofiberSequenceFunctor F ⋙ CofiberSequenceCategory.quotient D).obj S =
        ((CofiberSequenceCategory.quotient C ⋙ F).obj S)))).hom := rfl
  rw [h]
  rfl

/-- Underlying diagram component of stage-two naturality at `A : Ar 2`.

On diagonals the comparison is `F.mapZeroObject.symm`; off diagonal it is
the identity between the two presentations of `F.obj X`, `F.obj Y`, and
`F.obj Z`. -/
noncomputable def stageTwoNaturalityUnderlyingAppIso (S : CofiberSequenceCategory C)
    (A : Ar 2) :
    (((cofiberSequenceFunctor F ⋙ stageTwoFunctor D).obj S).obj.obj A) ≅
      (((stageTwoFunctor C ⋙ mapStage C D F 2).obj S).obj.obj A) := by
  by_cases ha : A.left = A.right
  · have hL0 : (((cofiberSequenceFunctor F ⋙ stageTwoFunctor D).obj S).obj.obj A) =
        stageTwoDiagramObj D (F.obj (S.obj.obj' 0)) (F.obj (S.obj.obj' 1))
          (F.obj (S.obj.obj' 2)) A := rfl
    have hDiagL : stageTwoDiagramObj D (F.obj (S.obj.obj' 0))
        (F.obj (S.obj.obj' 1)) (F.obj (S.obj.obj' 2)) A = (0 : D) :=
      stageTwoDiagramObj_of_eq D _ _ _ ha
    have hL : (((cofiberSequenceFunctor F ⋙ stageTwoFunctor D).obj S).obj.obj A) =
        (0 : D) := hL0.trans hDiagL
    have hR0 : (((stageTwoFunctor C ⋙ mapStage C D F 2).obj S).obj.obj A) =
        F.obj (stageTwoDiagramObj C (S.obj.obj' 0) (S.obj.obj' 1)
          (S.obj.obj' 2) A) := rfl
    have hDiagC : stageTwoDiagramObj C (S.obj.obj' 0) (S.obj.obj' 1)
        (S.obj.obj' 2) A = (0 : C) :=
      stageTwoDiagramObj_of_eq C _ _ _ ha
    have hR : (((stageTwoFunctor C ⋙ mapStage C D F 2).obj S).obj.obj A) =
        F.obj (0 : C) := hR0.trans (congrArg F.obj hDiagC)
    rw [hL, hR]
    exact F.mapZeroObject.symm
  · by_cases ha01 : A.left.val = 0 ∧ A.right.val = 1
    · have hL0 : (((cofiberSequenceFunctor F ⋙ stageTwoFunctor D).obj S).obj.obj A) =
          stageTwoDiagramObj D (F.obj (S.obj.obj' 0)) (F.obj (S.obj.obj' 1))
            (F.obj (S.obj.obj' 2)) A := rfl
      have h01L : stageTwoDiagramObj D (F.obj (S.obj.obj' 0))
          (F.obj (S.obj.obj' 1)) (F.obj (S.obj.obj' 2)) A =
          F.obj (S.obj.obj' 0) :=
        stageTwoDiagramObj_of_01 D _ _ _ ha ha01
      have hL : (((cofiberSequenceFunctor F ⋙ stageTwoFunctor D).obj S).obj.obj A) =
          F.obj (S.obj.obj' 0) := hL0.trans h01L
      have hR0 : (((stageTwoFunctor C ⋙ mapStage C D F 2).obj S).obj.obj A) =
          F.obj (stageTwoDiagramObj C (S.obj.obj' 0) (S.obj.obj' 1)
            (S.obj.obj' 2) A) := rfl
      have h01C : stageTwoDiagramObj C (S.obj.obj' 0) (S.obj.obj' 1)
          (S.obj.obj' 2) A = S.obj.obj' 0 :=
        stageTwoDiagramObj_of_01 C _ _ _ ha ha01
      have hR : (((stageTwoFunctor C ⋙ mapStage C D F 2).obj S).obj.obj A) =
          F.obj (S.obj.obj' 0) := hR0.trans (congrArg F.obj h01C)
      rw [hL, hR]
    · by_cases ha02 : A.left.val = 0 ∧ A.right.val = 2
      · have hL0 : (((cofiberSequenceFunctor F ⋙ stageTwoFunctor D).obj S).obj.obj A) =
            stageTwoDiagramObj D (F.obj (S.obj.obj' 0)) (F.obj (S.obj.obj' 1))
              (F.obj (S.obj.obj' 2)) A := rfl
        have h02L : stageTwoDiagramObj D (F.obj (S.obj.obj' 0))
            (F.obj (S.obj.obj' 1)) (F.obj (S.obj.obj' 2)) A =
            F.obj (S.obj.obj' 1) :=
          stageTwoDiagramObj_of_02 D _ _ _ ha ha01 ha02
        have hL : (((cofiberSequenceFunctor F ⋙ stageTwoFunctor D).obj S).obj.obj A) =
            F.obj (S.obj.obj' 1) := hL0.trans h02L
        have hR0 : (((stageTwoFunctor C ⋙ mapStage C D F 2).obj S).obj.obj A) =
            F.obj (stageTwoDiagramObj C (S.obj.obj' 0) (S.obj.obj' 1)
              (S.obj.obj' 2) A) := rfl
        have h02C : stageTwoDiagramObj C (S.obj.obj' 0) (S.obj.obj' 1)
            (S.obj.obj' 2) A = S.obj.obj' 1 :=
          stageTwoDiagramObj_of_02 C _ _ _ ha ha01 ha02
        have hR : (((stageTwoFunctor C ⋙ mapStage C D F 2).obj S).obj.obj A) =
            F.obj (S.obj.obj' 1) := hR0.trans (congrArg F.obj h02C)
        rw [hL, hR]
      · have hL0 : (((cofiberSequenceFunctor F ⋙ stageTwoFunctor D).obj S).obj.obj A) =
            stageTwoDiagramObj D (F.obj (S.obj.obj' 0)) (F.obj (S.obj.obj' 1))
              (F.obj (S.obj.obj' 2)) A := rfl
        have h12L : stageTwoDiagramObj D (F.obj (S.obj.obj' 0))
            (F.obj (S.obj.obj' 1)) (F.obj (S.obj.obj' 2)) A =
            F.obj (S.obj.obj' 2) :=
          stageTwoDiagramObj_of_12 D _ _ _ ha ha01 ha02
        have hL : (((cofiberSequenceFunctor F ⋙ stageTwoFunctor D).obj S).obj.obj A) =
            F.obj (S.obj.obj' 2) := hL0.trans h12L
        have hR0 : (((stageTwoFunctor C ⋙ mapStage C D F 2).obj S).obj.obj A) =
            F.obj (stageTwoDiagramObj C (S.obj.obj' 0) (S.obj.obj' 1)
              (S.obj.obj' 2) A) := rfl
        have h12C : stageTwoDiagramObj C (S.obj.obj' 0) (S.obj.obj' 1)
            (S.obj.obj' 2) A = S.obj.obj' 2 :=
          stageTwoDiagramObj_of_12 C _ _ _ ha ha01 ha02
        have hR : (((stageTwoFunctor C ⋙ mapStage C D F 2).obj S).obj.obj A) =
            F.obj (S.obj.obj' 2) := hR0.trans (congrArg F.obj h12C)
        rw [hL, hR]

/-- Underlying diagram isomorphism of stage-two naturality at `S`. -/
noncomputable def stageTwoNaturalityUnderlyingIso (S : CofiberSequenceCategory C) :
    (((cofiberSequenceFunctor F ⋙ stageTwoFunctor D).obj S).obj) ≅
      (((stageTwoFunctor C ⋙ mapStage C D F 2).obj S).obj) :=
  NatIso.ofComponents (stageTwoNaturalityUnderlyingAppIso F S) (by
    intro A B f
    by_cases ha : A.left = A.right
    · have hL0 : (((cofiberSequenceFunctor F ⋙ stageTwoFunctor D).obj S).obj.obj A) =
          stageTwoDiagramObj D (F.obj (S.obj.obj' 0)) (F.obj (S.obj.obj' 1))
            (F.obj (S.obj.obj' 2)) A := rfl
      have hDiagL : stageTwoDiagramObj D (F.obj (S.obj.obj' 0))
          (F.obj (S.obj.obj' 1)) (F.obj (S.obj.obj' 2)) A = (0 : D) :=
        stageTwoDiagramObj_of_eq D _ _ _ ha
      have hL : (((cofiberSequenceFunctor F ⋙ stageTwoFunctor D).obj S).obj.obj A) =
          (0 : D) := hL0.trans hDiagL
      have hZ : IsZero (((cofiberSequenceFunctor F ⋙ stageTwoFunctor D).obj S).obj.obj A) :=
        hL.symm ▸ isZero_zero D
      exact hZ.eq_of_src _ _
    · by_cases hb : B.left = B.right
      · have hR0 : (((stageTwoFunctor C ⋙ mapStage C D F 2).obj S).obj.obj B) =
            F.obj (stageTwoDiagramObj C (S.obj.obj' 0) (S.obj.obj' 1)
              (S.obj.obj' 2) B) := rfl
        have hDiagC : stageTwoDiagramObj C (S.obj.obj' 0) (S.obj.obj' 1)
            (S.obj.obj' 2) B = (0 : C) :=
          stageTwoDiagramObj_of_eq C _ _ _ hb
        have hR : (((stageTwoFunctor C ⋙ mapStage C D F 2).obj S).obj.obj B) =
            F.obj (0 : C) :=
          hR0.trans (congrArg F.obj hDiagC)
        have hF0 : IsZero (F.obj (0 : C)) := F.map_isZero (isZero_zero C)
        have hZ : IsZero (((stageTwoFunctor C ⋙ mapStage C D F 2).obj S).obj.obj B) :=
          hR.symm ▸ hF0
        exact hZ.eq_of_tgt _ _
      · by_cases ha01 : A.left.val = 0 ∧ A.right.val = 1
        · by_cases hb01 : B.left.val = 0 ∧ B.right.val = 1
          · have hA : A = interval (0 : Fin 3) 1 (by decide) :=
              stageTwo_ar2_eq_interval01 ha01
            have hB : B = interval (0 : Fin 3) 1 (by decide) :=
              stageTwo_ar2_eq_interval01 hb01
            subst hA
            subst hB
            have hf : f = 𝟙 _ :=
              Arrow.hom_ext _ _ (Subsingleton.elim _ _) (Subsingleton.elim _ _)
            subst hf
            simp
          · by_cases hb02 : B.left.val = 0 ∧ B.right.val = 2
            · have hA : A = interval (0 : Fin 3) 1 (by decide) :=
                stageTwo_ar2_eq_interval01 ha01
              have hB : B = interval (0 : Fin 3) 2 (by decide) :=
                stageTwo_ar2_eq_interval02 hb02
              subst hA
              subst hB
              -- Off-diagonal `01 → 02`: both comparisons are `𝟙` by the
              -- `stageTwoDiagramObj_of_01/02` identities; maps agree by the
              -- `stageTwoFunctor`/`mapStage` object+map laws.
              change F.map (S.obj.map' 0 1) ≫ 𝟙 _ = 𝟙 _ ≫ F.map (S.obj.map' 0 1)
              exact (Category.comp_id _).trans (Category.id_comp _).symm
            · have hA : A = interval (0 : Fin 3) 1 (by decide) :=
                stageTwo_ar2_eq_interval01 ha01
              have hB : B = interval (1 : Fin 3) 2 (by decide) :=
                stageTwo_ar2_eq_interval12 hb hb01 hb02
              subst hA
              subst hB
              -- Off-diagonal `01 → 12`: comparisons are `𝟙` by the
              -- `stageTwoDiagramObj_of_01/12` identities; the `D`-side map is
              -- the composite of the `F`-mapped legs while the `mapStage` side
              -- is `F` of the composite, reconciled by `Functor.map_comp`.
              change (F.map (S.obj.map' 0 1) ≫ F.map (S.obj.map' 1 2)) ≫ 𝟙 _ =
                𝟙 _ ≫ F.map (S.obj.map' 0 1 ≫ S.obj.map' 1 2)
              rw [← Functor.map_comp]
              exact (Category.comp_id _).trans (Category.id_comp _).symm
        · by_cases ha02 : A.left.val = 0 ∧ A.right.val = 2
          · by_cases hb01 : B.left.val = 0 ∧ B.right.val = 1
            · exfalso
              have hA : A = interval (0 : Fin 3) 2 (by decide) :=
                stageTwo_ar2_eq_interval02 ha02
              have hB : B = interval (0 : Fin 3) 1 (by decide) :=
                stageTwo_ar2_eq_interval01 hb01
              subst hA
              subst hB
              have hle : (2 : Fin 3) ≤ (1 : Fin 3) := leOfHom f.right
              exact absurd hle (by decide)
            · by_cases hb02 : B.left.val = 0 ∧ B.right.val = 2
              · have hA : A = interval (0 : Fin 3) 2 (by decide) :=
                  stageTwo_ar2_eq_interval02 ha02
                have hB : B = interval (0 : Fin 3) 2 (by decide) :=
                  stageTwo_ar2_eq_interval02 hb02
                subst hA
                subst hB
                have hf : f = 𝟙 _ :=
                  Arrow.hom_ext _ _ (Subsingleton.elim _ _) (Subsingleton.elim _ _)
                subst hf
                simp
              · have hA : A = interval (0 : Fin 3) 2 (by decide) :=
                  stageTwo_ar2_eq_interval02 ha02
                have hB : B = interval (1 : Fin 3) 2 (by decide) :=
                  stageTwo_ar2_eq_interval12 hb hb01 hb02
                subst hA
                subst hB
                -- Off-diagonal `02 → 12`: both comparisons are `𝟙` by the
                -- `stageTwoDiagramObj_of_02/12` identities; maps agree by the
                -- `stageTwoFunctor`/`mapStage` object+map laws.
                change F.map (S.obj.map' 1 2) ≫ 𝟙 _ = 𝟙 _ ≫ F.map (S.obj.map' 1 2)
                exact (Category.comp_id _).trans (Category.id_comp _).symm
          · by_cases hb01 : B.left.val = 0 ∧ B.right.val = 1
            · exfalso
              have hA : A = interval (1 : Fin 3) 2 (by decide) :=
                stageTwo_ar2_eq_interval12 ha ha01 ha02
              have hB : B = interval (0 : Fin 3) 1 (by decide) :=
                stageTwo_ar2_eq_interval01 hb01
              subst hA
              subst hB
              have hleL : (1 : Fin 3) ≤ (0 : Fin 3) := leOfHom f.left
              exact absurd hleL (by decide)
            · by_cases hb02 : B.left.val = 0 ∧ B.right.val = 2
              · exfalso
                have hA : A = interval (1 : Fin 3) 2 (by decide) :=
                  stageTwo_ar2_eq_interval12 ha ha01 ha02
                have hB : B = interval (0 : Fin 3) 2 (by decide) :=
                  stageTwo_ar2_eq_interval02 hb02
                subst hA
                subst hB
                have hleL : (1 : Fin 3) ≤ (0 : Fin 3) := leOfHom f.left
                exact absurd hleL (by decide)
              · have hA : A = interval (1 : Fin 3) 2 (by decide) :=
                  stageTwo_ar2_eq_interval12 ha ha01 ha02
                have hB : B = interval (1 : Fin 3) 2 (by decide) :=
                  stageTwo_ar2_eq_interval12 hb hb01 hb02
                subst hA
                subst hB
                have hf : f = 𝟙 _ :=
                  Arrow.hom_ext _ _ (Subsingleton.elim _ _) (Subsingleton.elim _ _)
                subst hf
                simp)

/-- Stage-level component of stage-two naturality at `S`. -/
noncomputable def stageTwoNaturalityAppIso (S : CofiberSequenceCategory C) :
    (cofiberSequenceFunctor F ⋙ stageTwoFunctor D).obj S ≅
      (stageTwoFunctor C ⋙ mapStage C D F 2).obj S :=
  ObjectProperty.isoMk _ (stageTwoNaturalityUnderlyingIso F S)

/-- Stage-two naturality: staging after the cofiber lift agrees with
postcomposition after staging. -/
noncomputable def stageTwoNaturalityIso :
    cofiberSequenceFunctor F ⋙ stageTwoFunctor D ≅
      stageTwoFunctor C ⋙ mapStage C D F 2 :=
  NatIso.ofComponents (stageTwoNaturalityAppIso F) (by
    intro S T φ
    apply ObjectProperty.hom_ext
    ext A
    by_cases ha : A.left = A.right
    · have hL0 : (((cofiberSequenceFunctor F ⋙ stageTwoFunctor D).obj S).obj.obj A) =
          stageTwoDiagramObj D (F.obj (S.obj.obj' 0)) (F.obj (S.obj.obj' 1))
            (F.obj (S.obj.obj' 2)) A := rfl
      have hDiagL : stageTwoDiagramObj D (F.obj (S.obj.obj' 0))
          (F.obj (S.obj.obj' 1)) (F.obj (S.obj.obj' 2)) A = (0 : D) :=
        stageTwoDiagramObj_of_eq D _ _ _ ha
      have hL : (((cofiberSequenceFunctor F ⋙ stageTwoFunctor D).obj S).obj.obj A) =
          (0 : D) := hL0.trans hDiagL
      have hZ : IsZero (((cofiberSequenceFunctor F ⋙ stageTwoFunctor D).obj S).obj.obj A) :=
        hL.symm ▸ isZero_zero D
      exact hZ.eq_of_src _ _
    · by_cases ha01 : A.left.val = 0 ∧ A.right.val = 1
      · have hA : A = interval (0 : Fin 3) 1 (by decide) :=
          stageTwo_ar2_eq_interval01 ha01
        subst hA
        -- Lifted `01`: comparisons are `𝟙`; maps agree by
        -- `stageTwoFunctor_map_01` and `mapStage_map` with the `01` interval.
        change F.map (ComposableArrows.app' φ.hom 0) ≫ 𝟙 _ =
          𝟙 _ ≫ F.map (ComposableArrows.app' φ.hom 0)
        exact (Category.comp_id _).trans (Category.id_comp _).symm
      · by_cases ha02 : A.left.val = 0 ∧ A.right.val = 2
        · have hA : A = interval (0 : Fin 3) 2 (by decide) :=
            stageTwo_ar2_eq_interval02 ha02
          subst hA
          -- Lifted `02`: comparisons are `𝟙`; maps agree by
          -- `stageTwoFunctor_map_02` and `mapStage_map` with the `02` interval.
          change F.map (ComposableArrows.app' φ.hom 1) ≫ 𝟙 _ =
            𝟙 _ ≫ F.map (ComposableArrows.app' φ.hom 1)
          exact (Category.comp_id _).trans (Category.id_comp _).symm
        · have hA : A = interval (1 : Fin 3) 2 (by decide) :=
            stageTwo_ar2_eq_interval12 ha ha01 ha02
          subst hA
          -- Lifted `12`: comparisons are `𝟙`; maps agree by
          -- `stageTwoFunctor_map_12` and `mapStage_map` with the `12` interval.
          change F.map (ComposableArrows.app' φ.hom 2) ≫ 𝟙 _ =
            𝟙 _ ≫ F.map (ComposableArrows.app' φ.hom 2)
          exact (Category.comp_id _).trans (Category.id_comp _).symm)

end CategoryTheory.Waldhausen.SConstruction
