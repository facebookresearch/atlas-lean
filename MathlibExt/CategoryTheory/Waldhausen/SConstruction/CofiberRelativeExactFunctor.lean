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

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.CofiberRelativeEvaluation
public import MathlibExt.CategoryTheory.Waldhausen.ExactFunctor
public import Mathlib.CategoryTheory.ComposableArrows.Basic

/-!
# Original relative cofiber functors for arbitrary Waldhausen exact functors

Postcomposition by an original Waldhausen exact functor acts on the actual
cofiber-sequence categories. The original raw relative corner is sent to
the image pushout corner, with the same original corner map. This proves
exactness for the original named relative structures, including all zero,
weak-equivalence and pushout fields, in independent source and target
universes. No exact-category or levelwise replacement is used.
-/

public section

open CategoryTheory Limits

universe v₁ u₁ v₂ u₂

namespace CategoryTheory.Waldhausen.SConstruction.CofiberSequenceCategory

variable {C : Type u₁} [Category.{v₁} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]
variable {D : Type u₂} [Category.{v₂} D] [HasZeroObject D] [WaldhausenCategoryWithoutGluing D]

/-- The original finite cofiber row is postcomposed by the given
Waldhausen exact functor, retaining its whole diagram and maps. -/
noncomputable def mapOfWaldhausenExact (F : C ⥤ D) (hF : F.IsWaldhausenExact) :
    CofiberSequenceCategory C ⥤ CofiberSequenceCategory D :=
  (cofiberSequenceProperty D).lift
    (forget C ⋙ F.mapComposableArrows 2)
    (fun S => hF.map_cofibrationSequence S.property)

private theorem mapOfWaldhausenExact_obj_computed (F : C ⥤ D) (hF : F.IsWaldhausenExact)
    (S : CofiberSequenceCategory C) :
    ((mapOfWaldhausenExact F hF).obj S).obj = S.obj ⋙ F := by
  unfold mapOfWaldhausenExact
  rfl

private theorem mapOfWaldhausenExact_map_computed_heq (F : C ⥤ D) (hF : F.IsWaldhausenExact)
    {S T : CofiberSequenceCategory C} (f : S ⟶ T) :
    HEq ((mapOfWaldhausenExact F hF).map f).hom (Functor.whiskerRight f.hom F) := by
  unfold mapOfWaldhausenExact
  rfl

/-- The entire underlying original cofiber diagram is postcomposition. -/
theorem mapOfWaldhausenExact_obj (F : C ⥤ D) (hF : F.IsWaldhausenExact)
    (S : CofiberSequenceCategory C) :
    ((mapOfWaldhausenExact F hF).obj S).obj = S.obj ⋙ F :=
  mapOfWaldhausenExact_obj_computed F hF S

/-- The WHOLE underlying original cofiber morphism is the original
postwhiskering, through its complete original source and target diagrams. -/
theorem mapOfWaldhausenExact_map_heq (F : C ⥤ D) (hF : F.IsWaldhausenExact)
    {S T : CofiberSequenceCategory C} (f : S ⟶ T) :
    HEq ((mapOfWaldhausenExact F hF).map f).hom (Functor.whiskerRight f.hom F) :=
  mapOfWaldhausenExact_map_computed_heq F hF f

/-- The same WHOLE original map has the typed postwhiskering equality
after the exact original source/target diagram equality transports. -/
theorem mapOfWaldhausenExact_map (F : C ⥤ D) (hF : F.IsWaldhausenExact)
    {S T : CofiberSequenceCategory C} (f : S ⟶ T) :
    eqToHom (mapOfWaldhausenExact_obj F hF S).symm ≫
        ((mapOfWaldhausenExact F hF).map f).hom ≫
        eqToHom (mapOfWaldhausenExact_obj F hF T) =
      Functor.whiskerRight f.hom F :=
  ((conj_eqToHom_iff_heq _ _ (mapOfWaldhausenExact_obj F hF S).symm
    (mapOfWaldhausenExact_obj F hF T).symm).mpr
      (mapOfWaldhausenExact_map_heq F hF f).symm).symm

private theorem mapOfWaldhausenExact_relative_raw_computed
    (F : C ⥤ D) (hF : F.IsWaldhausenExact)
    {S T : CofiberSequenceCategory C} (f : S ⟶ T) :
    relativeCofibrations D ((mapOfWaldhausenExact F hF).map f) ↔
      IsCofibration (F.map (f.hom.app (0 : Fin 3))) ∧
        ∃ (Q : D) (inB : F.obj (S.obj.obj' 1) ⟶ Q)
          (inA : F.obj (T.obj.obj' 0) ⟶ Q) (d : Q ⟶ F.obj (T.obj.obj' 1)),
          IsPushout (F.map (S.obj.map' 0 1)) (F.map (f.hom.app (0 : Fin 3))) inB inA ∧
            inB ≫ d = F.map (f.hom.app (1 : Fin 3)) ∧
            inA ≫ d = F.map (T.obj.map' 0 1) ∧ IsCofibration d := by
  unfold mapOfWaldhausenExact
  rw [mem_relativeCofibrations_raw_iff]
  rfl

/-- The exact mapped relative predicate retains ALL original image
corner objects, both image legs, image d and both complete triangles. -/
theorem mapOfWaldhausenExact_relativeCofibrations_raw_iff
    (F : C ⥤ D) (hF : F.IsWaldhausenExact)
    {S T : CofiberSequenceCategory C} (f : S ⟶ T) :
    relativeCofibrations D ((mapOfWaldhausenExact F hF).map f) ↔
      IsCofibration (F.map (f.hom.app (0 : Fin 3))) ∧
        ∃ (Q : D) (inB : F.obj (S.obj.obj' 1) ⟶ Q)
          (inA : F.obj (T.obj.obj' 0) ⟶ Q) (d : Q ⟶ F.obj (T.obj.obj' 1)),
          IsPushout (F.map (S.obj.map' 0 1)) (F.map (f.hom.app (0 : Fin 3))) inB inA ∧
            inB ≫ d = F.map (f.hom.app (1 : Fin 3)) ∧
            inA ≫ d = F.map (T.obj.map' 0 1) ∧ IsCofibration d :=
  mapOfWaldhausenExact_relative_raw_computed F hF f

private theorem mapOfWaldhausenExact_weak_raw_computed
    (F : C ⥤ D) (hF : F.IsWaldhausenExact)
    {S T : CofiberSequenceCategory C} (f : S ⟶ T) :
    levelwiseWeakEquivalences D ((mapOfWaldhausenExact F hF).map f) ↔
      IsWeakEquivalence (F.map (f.hom.app (0 : Fin 3))) ∧
      IsWeakEquivalence (F.map (f.hom.app (1 : Fin 3))) ∧
        IsWeakEquivalence (F.map (f.hom.app (2 : Fin 3))) := by
  unfold mapOfWaldhausenExact
  rw [mem_levelwiseWeakEquivalences_iff, source_map, middle_map, quotient_map]
  rfl

/-- The exact mapped weak predicate retains all THREE original image
morphisms, without unfolding the exported cofiber functor in a consumer. -/
theorem mapOfWaldhausenExact_levelwiseWeakEquivalences_raw_iff
    (F : C ⥤ D) (hF : F.IsWaldhausenExact)
    {S T : CofiberSequenceCategory C} (f : S ⟶ T) :
    levelwiseWeakEquivalences D ((mapOfWaldhausenExact F hF).map f) ↔
      IsWeakEquivalence (F.map (f.hom.app (0 : Fin 3))) ∧
      IsWeakEquivalence (F.map (f.hom.app (1 : Fin 3))) ∧
        IsWeakEquivalence (F.map (f.hom.app (2 : Fin 3))) :=
  mapOfWaldhausenExact_weak_raw_computed F hF f

/-- Every original relative corner is sent to its actual image
pushout corner, with the SAME original whole corner map under F. -/
theorem mapOfWaldhausenExact_relativeCofibrations (F : C ⥤ D) (hF : F.IsWaldhausenExact)
    {S T : CofiberSequenceCategory C} (f : S ⟶ T) (hf : relativeCofibrations C f) :
    relativeCofibrations D ((mapOfWaldhausenExact F hF).map f) := by
  obtain ⟨hf₀, P, inB, inA, d, hP, hB, hA, hd⟩ :=
    (mem_relativeCofibrations_raw_iff C f).mp hf
  apply (mem_relativeCofibrations_raw_iff D _).mpr
  change IsCofibration (F.map (f.hom.app (0 : Fin 3))) ∧
    ∃ (Q : D) (inB' : F.obj (S.obj.obj' 1) ⟶ Q)
      (inA' : F.obj (T.obj.obj' 0) ⟶ Q) (d' : Q ⟶ F.obj (T.obj.obj' 1)),
      IsPushout (F.map (S.obj.map' 0 1)) (F.map (f.hom.app (0 : Fin 3))) inB' inA' ∧
        inB' ≫ d' = F.map (f.hom.app (1 : Fin 3)) ∧
        inA' ≫ d' = F.map (T.obj.map' 0 1) ∧ IsCofibration d'
  refine ⟨hF.map_cofibration _ hf₀, F.obj P, F.map inB, F.map inA, F.map d,
    ?_, ?_, ?_, hF.map_cofibration d hd⟩
  · exact (hF.map_pushout (S.obj.map' 0 1) (f.hom.app (0 : Fin 3))
      inA inB S.property.1 hP.flip).flip
  · simpa only [Functor.map_comp] using F.congr_map hB
  · simpa only [Functor.map_comp] using F.congr_map hA

/-- The original cofiber lift is exact for the two SAME named relative
Waldhausen structures; all four fields are derived from original F. -/
theorem mapOfWaldhausenExact_isRelativeWaldhausenExact
    (F : C ⥤ D) (hF : F.IsWaldhausenExact) :
    letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C;
    letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory D) :=
      relativeWaldhausenCategory D;
    (mapOfWaldhausenExact F hF).IsWaldhausenExact := by
  let : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) := relativeWaldhausenCategory C
  let : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory D) := relativeWaldhausenCategory D
  refine { map_isZero := ?_, map_cofibration := ?_, map_weakEquivalence := ?_, map_pushout := ?_ }
  · intro X hX
    apply IsZero.of_full_of_faithful_of_isZero (forget D)
    apply Functor.isZero
    intro k
    change IsZero (F.obj (X.obj.obj k))
    exact hF.map_isZero ((evaluationIsRelativeWaldhausenExact C k).map_isZero hX)
  · intro S T f hf
    apply (isCofibration_relativeWaldhausenCategory_iff D _).mpr
    exact mapOfWaldhausenExact_relativeCofibrations F hF f
      ((isCofibration_relativeWaldhausenCategory_iff C f).mp hf)
  · intro S T f hf
    have h := (mem_levelwiseWeakEquivalences_iff C f).mp
      ((isWeakEquivalence_relativeWaldhausenCategory_iff C f).mp hf)
    apply (isWeakEquivalence_relativeWaldhausenCategory_iff D _).mpr
    apply (mem_levelwiseWeakEquivalences_iff D _).mpr
    change IsWeakEquivalence (F.map (f.hom.app (0 : Fin 3))) ∧
      IsWeakEquivalence (F.map (f.hom.app (1 : Fin 3))) ∧
        IsWeakEquivalence (F.map (f.hom.app (2 : Fin 3)))
    exact ⟨hF.map_weakEquivalence _ h.1,
      hF.map_weakEquivalence _ h.2.1, hF.map_weakEquivalence _ h.2.2⟩
  · intro X Y X' P i f inl inr hi hp
    apply IsPushout.of_map_of_faithful (forget D)
    apply IsPushout.of_forall_isPushout_app
    intro k
    have hik : IsCofibration (i.hom.app k) :=
      (evaluationIsRelativeWaldhausenExact C k).map_cofibration i hi
    have hpk : IsPushout (f.hom.app k) (i.hom.app k) (inl.hom.app k) (inr.hom.app k) :=
      (evaluationIsRelativeWaldhausenExact C k).map_pushout i f inl inr hi hp
    change IsPushout (F.map (f.hom.app k)) (F.map (i.hom.app k))
      (F.map (inl.hom.app k)) (F.map (inr.hom.app k))
    exact hF.map_pushout _ _ _ _ hik hpk

end CategoryTheory.Waldhausen.SConstruction.CofiberSequenceCategory
