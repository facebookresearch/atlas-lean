/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageTwoEquivalence
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWaldhausenExactFunctor
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.CofiberRelativeWaldhausen

/-!
# Exactness of the original relative cofiber and degree-two stage comparison

Both directions of the existing categorical equivalence preserve the
genuine relative corner cofibrations, the original weak components and
the whole original pushouts. The degree-two zero-row corners are the
actual source component and original relative pushout-corner witness.
The original category keeps independent object and morphism universes.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

universe u v uA vA uB vB

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace CategoryTheory.Waldhausen.SConstruction
namespace StageTwoRelativeWaldhausenExact

private theorem mapIsZero_of_equivalence
    {A : Type uA} [Category.{vA} A] [HasZeroObject A]
    {B : Type uB} [Category.{vB} B] [HasZeroObject B]
    (F : A ⥤ B) [F.IsEquivalence] {X : A} (hX : IsZero X) : IsZero (F.obj X) := by
  let : HasZeroMorphisms A := (isZero_zero A).hasZeroMorphisms
  let : HasZeroMorphisms B := (isZero_zero B).hasZeroMorphisms
  exact F.map_isZero hX

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

local instance originalStageZero : HasZeroObject (Stage C 2) := generalStageHasZeroObject C 2
local instance originalStageValue : WaldhausenCategoryWithoutGluing (Stage C 2) :=
  generalStageWaldhausenCategory C 2
local instance originalCofiberValue : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
  CofiberSequenceCategory.relativeWaldhausenCategory C

/-- The original staged source is the same whole original cofiber source functor. -/
theorem stageTwoFunctor_source :
    stageTwoFunctor C ⋙ eval C 2 (interval (0 : Fin 3) 1 (by decide)) =
      CofiberSequenceCategory.source C := rfl

/-- The original staged middle is the same whole original cofiber middle functor. -/
theorem stageTwoFunctor_middle :
    stageTwoFunctor C ⋙ eval C 2 (interval (0 : Fin 3) 2 (by decide)) =
      CofiberSequenceCategory.middle C := rfl

/-- The original staged quotient is the same whole original cofiber quotient functor. -/
theorem stageTwoFunctor_quotient :
    stageTwoFunctor C ⋙ eval C 2 (interval (1 : Fin 3) 2 (by decide)) =
      CofiberSequenceCategory.quotient C := rfl

/-- The original extracted source is the actual `(0,1)` stage evaluation. -/
theorem stageTwoExtraction_source :
    stageTwoExtraction C ⋙ CofiberSequenceCategory.source C =
      eval C 2 (interval (0 : Fin 3) 1 (by decide)) := rfl

/-- The original extracted middle is the actual `(0,2)` stage evaluation. -/
theorem stageTwoExtraction_middle :
    stageTwoExtraction C ⋙ CofiberSequenceCategory.middle C =
      eval C 2 (interval (0 : Fin 3) 2 (by decide)) := rfl

/-- The original extracted quotient is the actual `(1,2)` stage evaluation. -/
theorem stageTwoExtraction_quotient :
    stageTwoExtraction C ⋙ CofiberSequenceCategory.quotient C =
      eval C 2 (interval (1 : Fin 3) 2 (by decide)) := rfl

private theorem firstCorner {A B : Stage C 2} (f : A ⟶ B)
    (hf : IsCofibration (Stage.zeroRowApp f (1 : Fin 3))) :
    ∃ (P : C) (l : A.zeroRowObj (1 : Fin 3) ⟶ P) (r : B.zeroRowObj (0 : Fin 3) ⟶ P)
      (d : P ⟶ B.zeroRowObj (1 : Fin 3)),
      IsPushout (A.zeroRowSuccMap (0 : Fin 2)) (Stage.zeroRowApp f (0 : Fin 3)) l r ∧
        l ≫ d = Stage.zeroRowApp f (1 : Fin 3) ∧ r ≫ d = B.zeroRowSuccMap (0 : Fin 2) ∧
        IsCofibration d := by
  have hA : IsZero (A.zeroRowObj (0 : Fin 3)) := A.property.diag_isZero 0
  have hB : IsZero (B.zeroRowObj (0 : Fin 3)) := B.property.diag_isZero 0
  let l : A.zeroRowObj (1 : Fin 3) ⟶ A.zeroRowObj (1 : Fin 3) := 𝟙 _
  let r : B.zeroRowObj (0 : Fin 3) ⟶ A.zeroRowObj (1 : Fin 3) := hB.to_ _
  let d := Stage.zeroRowApp f (1 : Fin 3)
  let : IsIso (Stage.zeroRowApp f (0 : Fin 3)) := hA.isIso hB _
  let : IsIso l := by dsimp only [l]; infer_instance
  have hp : IsPushout (A.zeroRowSuccMap (0 : Fin 2)) (Stage.zeroRowApp f (0 : Fin 3)) l r := by
    apply IsPushout.of_vert_isIso
    exact ⟨hA.eq_of_src _ _⟩
  exact ⟨A.zeroRowObj 1, l, r, d, hp, Category.id_comp _, hB.eq_of_src _ _, hf⟩

/-- The original stage-two forward preserves the genuine relative source and pushout corner. -/
theorem stageTwoFunctor_cofibrations {S T : CofiberSequenceCategory C} (f : S ⟶ T)
    (hf : CofiberSequenceCategory.relativeCofibrations C f) :
    stageCofibrations C 2 ((stageTwoFunctor C).map f) := by
  obtain ⟨h0, P, l, r, d, hp, hl, hr, hd⟩ :=
    (CofiberSequenceCategory.mem_relativeCofibrations_raw_iff C f).mp hf
  intro i
  fin_cases i
  · have hFirst : IsCofibration (Stage.zeroRowApp ((stageTwoFunctor C).map f) (1 : Fin 3)) := by
      change IsCofibration ((stageTwoFunctor C ⋙ eval C 2 (interval (0 : Fin 3) 1 (by
        decide))).map f)
      rw [stageTwoFunctor_source]
      exact h0
    exact firstCorner C ((stageTwoFunctor C).map f) hFirst
  · exact ⟨P, l, r, d, hp, hl, hr, hd⟩

/-- The actual extraction reads the genuine source component and the same original second corner. -/
theorem stageTwoExtraction_cofibrations {A B : Stage C 2} (f : A ⟶ B)
    (hf : stageCofibrations C 2 f) :
    CofiberSequenceCategory.relativeCofibrations C ((stageTwoExtraction C).map f) := by
  apply (CofiberSequenceCategory.mem_relativeCofibrations_raw_iff C _).mpr
  refine ⟨?_, ?_⟩
  · exact Stage.intervalApp_isCofibration C f hf (0 : Fin 3) 1 (by decide)
  · exact hf (1 : Fin 2)

/-- The actual forward weak map keeps the three original sequence maps and the actual zero
diagonals. -/
theorem stageTwoFunctor_weak {S T : CofiberSequenceCategory C} (f : S ⟶ T)
    (hf : CofiberSequenceCategory.levelwiseWeakEquivalences C f) :
    stageWeak C 2 ((stageTwoFunctor C).map f) := by
  rw [mem_stageWeak]
  rw [CofiberSequenceCategory.mem_levelwiseWeakEquivalences_iff] at hf
  intro a
  by_cases ha : a.left = a.right
  · rw [stageTwo_ar2_eq_diag_of_eq ha]
    let : IsIso ((eval C 2 (diag a.left)).map ((stageTwoFunctor C).map f)) :=
      (((stageTwoFunctor C).obj S).property.diag_isZero a.left).isIso
        (((stageTwoFunctor C).obj T).property.diag_isZero a.left) _
    exact (WaldhausenCategoryWithoutGluing.weakEquivalences (C := C)).of_isIso _
  · by_cases h01 : a.left.val = 0 ∧ a.right.val = 1
    · rw [stageTwo_ar2_eq_interval01 h01]
      change IsWeakEquivalence ((stageTwoFunctor C ⋙ eval C 2 (interval (0 : Fin 3) 1 (by
        decide))).map f)
      rw [stageTwoFunctor_source]
      exact hf.1
    · by_cases h02 : a.left.val = 0 ∧ a.right.val = 2
      · rw [stageTwo_ar2_eq_interval02 h02]
        change IsWeakEquivalence ((stageTwoFunctor C ⋙ eval C 2 (interval (0 : Fin 3) 2
          (by decide))).map f)
        rw [stageTwoFunctor_middle]
        exact hf.2.1
      · rw [stageTwo_ar2_eq_interval12 ha h01 h02]
        change IsWeakEquivalence ((stageTwoFunctor C ⋙ eval C 2 (interval (1 : Fin 3) 2
          (by decide))).map f)
        rw [stageTwoFunctor_quotient]
        exact hf.2.2

/-- The original extraction takes exactly the three original weak interval components. -/
theorem stageTwoExtraction_weak {A B : Stage C 2} (f : A ⟶ B) (hf : stageWeak C 2 f) :
    CofiberSequenceCategory.levelwiseWeakEquivalences C ((stageTwoExtraction C).map f) := by
  rw [CofiberSequenceCategory.mem_levelwiseWeakEquivalences_iff]
  rw [mem_stageWeak] at hf
  refine ⟨?_, ?_, ?_⟩
  · change IsWeakEquivalence ((stageTwoExtraction C ⋙ CofiberSequenceCategory.source C).map f)
    rw [stageTwoExtraction_source]
    exact hf (interval (0 : Fin 3) 1 (by decide))
  · change IsWeakEquivalence ((stageTwoExtraction C ⋙ CofiberSequenceCategory.middle C).map f)
    rw [stageTwoExtraction_middle]
    exact hf (interval (0 : Fin 3) 2 (by decide))
  · change IsWeakEquivalence ((stageTwoExtraction C ⋙ CofiberSequenceCategory.quotient C).map f)
    rw [stageTwoExtraction_quotient]
    exact hf (interval (1 : Fin 3) 2 (by decide))

/-- The same original forward is exact for the genuine relative cofiber and general stage values. -/
theorem stageTwoFunctor_exact : (stageTwoFunctor C).IsWaldhausenExact := by
  let : (stageTwoFunctor C).IsEquivalence := (stageTwoEquivalence C).isEquivalence_functor
  constructor
  · intro S hS
    exact mapIsZero_of_equivalence (stageTwoFunctor C) hS
  · intro S T f hf
    exact (isCofibration_generalStageWaldhausenCategory_iff C 2 _).mpr
      (stageTwoFunctor_cofibrations C f
        ((CofiberSequenceCategory.isCofibration_relativeWaldhausenCategory_iff C f).mp hf))
  · intro S T f hf
    exact (isWeakEquivalence_generalStageWaldhausenCategory_iff C 2 _).mpr
      (stageTwoFunctor_weak C f
        ((CofiberSequenceCategory.isWeakEquivalence_relativeWaldhausenCategory_iff C f).mp hf))
  · intro S T S' P i f l r _hi hp
    exact hp.map (stageTwoFunctor C)

/-- The same original extraction is exact in the reverse direction for those two original values. -/
theorem stageTwoExtraction_exact : (stageTwoExtraction C).IsWaldhausenExact := by
  let : (stageTwoExtraction C).IsEquivalence := (stageTwoEquivalence C).isEquivalence_inverse
  constructor
  · intro A hA
    exact mapIsZero_of_equivalence (stageTwoExtraction C) hA
  · intro A B f hf
    exact (CofiberSequenceCategory.isCofibration_relativeWaldhausenCategory_iff C _).mpr
      (stageTwoExtraction_cofibrations C f
        ((isCofibration_generalStageWaldhausenCategory_iff C 2 f).mp hf))
  · intro A B f hf
    exact (CofiberSequenceCategory.isWeakEquivalence_relativeWaldhausenCategory_iff C _).mpr
      (stageTwoExtraction_weak C f
        ((isWeakEquivalence_generalStageWaldhausenCategory_iff C 2 f).mp hf))
  · intro A B A' P i f l r _hi hp
    exact hp.map (stageTwoExtraction C)

/-- Both original directions of the existing categorical comparison are genuinely Waldhausen
exact. -/
theorem stageTwoEquivalence_exact :
    (stageTwoEquivalence C).functor.IsWaldhausenExact ∧
      (stageTwoEquivalence C).inverse.IsWaldhausenExact :=
  ⟨stageTwoFunctor_exact C, stageTwoExtraction_exact C⟩

/-- The three original nondegenerate intervals of the degree-two stage. -/
def triangleCell : Fin 3 → Ar 2 :=
  ![interval (0 : Fin 3) 1 (by decide), interval (0 : Fin 3) 2 (by decide),
    interval (1 : Fin 3) 2 (by decide)]

/-- The actual original cofiber-side unit keeps every original column object. -/
theorem stageTwoUnit_column_object (S : CofiberSequenceCategory C) (k : Fin 3) :
    ((stageTwoFunctor C ⋙ stageTwoExtraction C).obj S).obj.obj k = S.obj.obj k := by
  fin_cases k <;> rfl

/-- The whole original forward unit column is its actual identity through the original
target object frame. -/
theorem stageTwoUnit_column_hom (S : CofiberSequenceCategory C) (k : Fin 3) :
    ((stageTwoUnit C).hom.app S).hom.app k ≫ eqToHom (stageTwoUnit_column_object C S k) =
      𝟙 (S.obj.obj k) := by
  fin_cases k <;> change 𝟙 _ ≫ 𝟙 _ = 𝟙 _ <;> exact Category.id_comp _

/-- The whole original inverse unit column keeps the reverse object frame and same original
identity. -/
theorem stageTwoUnit_column_inv (S : CofiberSequenceCategory C) (k : Fin 3) :
    eqToHom (stageTwoUnit_column_object C S k).symm ≫ ((stageTwoUnit C).inv.app S).hom.app k =
      𝟙 (S.obj.obj k) := by
  fin_cases k <;> change 𝟙 _ ≫ 𝟙 _ = 𝟙 _ <;> exact Category.id_comp _

/-- The actual original stage-side counit keeps each of the original source, middle and
quotient objects. -/
theorem stageTwoCounit_column_object (A : Stage C 2) (k : Fin 3) :
    ((stageTwoExtraction C ⋙ stageTwoFunctor C).obj A).obj.obj (triangleCell k) =
      A.obj.obj (triangleCell k) := by
  fin_cases k <;> rfl

/-- The same complete counit column is identity after its actual reverse source object frame. -/
theorem stageTwoCounit_column_hom (A : Stage C 2) (k : Fin 3) :
    eqToHom (stageTwoCounit_column_object C A k).symm ≫
        ((stageTwoCounit C).hom.app A).hom.app (triangleCell k) =
      𝟙 (A.obj.obj (triangleCell k)) := by
  fin_cases k <;> change 𝟙 _ ≫ 𝟙 _ = 𝟙 _ <;> exact Category.id_comp _

/-- The entire reverse counit column retains its same original target object frame. -/
theorem stageTwoCounit_column_inv (A : Stage C 2) (k : Fin 3) :
    ((stageTwoCounit C).inv.app A).hom.app (triangleCell k) ≫
        eqToHom (stageTwoCounit_column_object C A k) =
      𝟙 (A.obj.obj (triangleCell k)) := by
  fin_cases k <;> change 𝟙 _ ≫ 𝟙 _ = 𝟙 _ <;> exact Category.id_comp _

/-- The original counit on a zero diagonal is the unique map from the original chosen zero
to that same original diagonal zero object, through the actual source frame. -/
theorem stageTwoCounit_diagonal_hom (A : Stage C 2) (i : Fin 3) :
    eqToHom (stageTwoFunctor_obj_diag C ((stageTwoExtraction C).obj A) i).symm ≫
        ((stageTwoCounit C).hom.app A).hom.app (diag i) =
      (A.property.diag_isZero i).from_ (0 : C) :=
  (A.property.diag_isZero i).eq_of_tgt _ _

/-- The reverse original counit retains the unique map to the independently chosen base zero. -/
theorem stageTwoCounit_diagonal_inv (A : Stage C 2) (i : Fin 3) :
    ((stageTwoCounit C).inv.app A).hom.app (diag i) ≫
        eqToHom (stageTwoFunctor_obj_diag C ((stageTwoExtraction C).obj A) i) =
      (A.property.diag_isZero i).to_ (0 : C) :=
  (A.property.diag_isZero i).eq_of_src _ _

end StageTwoRelativeWaldhausenExact
end CategoryTheory.Waldhausen.SConstruction

end
