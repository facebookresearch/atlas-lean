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
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWaldhausenFunctoriality

/-!
# Coherent source, middle and quotient stages of general extensions

The actual exact evaluation functors for the named relative Waldhausen
value on E(C) act on every finite stage and its pointwise weak-equivalence
category. The existing mixed-universe Waldhausen stage construction is
reused. Its object, map, inclusion and reindex equations give the coherent
three evaluation families.

Only genuine relative E(C) stages are inputs. No converse from three
component stages or natural weak splitting of arbitrary extensions is
asserted.
-/

public section

open CategoryTheory Limits

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

namespace CofiberSequenceCategory

/-- Each original row evaluation carries a genuine relative E(C) stage
to a C-stage, by its derived Waldhausen exactness. -/
theorem isStage_relativeEvaluation (k : Fin 3) (n : ℕ)
    (A : Ar n ⥤ CofiberSequenceCategory C)
    (hA : (letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C; IsStage n A)) :
    IsStage n (A ⋙ ((forget C) ⋙ (evaluation (Fin 3) C).obj k)) := by
  let : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) := relativeWaldhausenCategory C
  exact (evaluationIsRelativeWaldhausenExact C k).isStage_postcomp n A hA

/-- The original source, middle and quotient diagrams of every genuine
relative E(C) stage are all C-stages. -/
theorem isStage_relativeEvaluations (n : ℕ)
    (A : Ar n ⥤ CofiberSequenceCategory C)
    (hA : (letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C; IsStage n A)) :
    IsStage n (A ⋙ source C) ∧ IsStage n (A ⋙ middle C) ∧
      IsStage n (A ⋙ quotient C) := by
  exact ⟨isStage_relativeEvaluation C 0 n A hA,
    isStage_relativeEvaluation C 1 n A hA,
    isStage_relativeEvaluation C 2 n A hA⟩

/-- The stage functor of an original row evaluation, using the same named
relative Waldhausen value throughout. -/
noncomputable def relativeEvaluationStage (k : Fin 3) (n : ℕ) :
    letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C;
    Stage (CofiberSequenceCategory C) n ⥤ Stage C n := by
  let : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) := relativeWaldhausenCategory C
  exact (evaluationIsRelativeWaldhausenExact C k).mapStage n

/-- The weak-stage restriction of the same original row evaluation. -/
noncomputable def relativeEvaluationWeakStage (k : Fin 3) (n : ℕ) :
    letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C;
    StageWeakCategory (CofiberSequenceCategory C) n ⥤ StageWeakCategory C n := by
  let : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) := relativeWaldhausenCategory C
  exact (evaluationIsRelativeWaldhausenExact C k).mapStageWeak n

/-- The actual source projection on all relative extension stages. -/
noncomputable def relativeSourceStage (n : ℕ) :
    letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C;
    Stage (CofiberSequenceCategory C) n ⥤ Stage C n :=
  relativeEvaluationStage C 0 n

/-- The actual middle projection on all relative extension stages. -/
noncomputable def relativeMiddleStage (n : ℕ) :
    letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C;
    Stage (CofiberSequenceCategory C) n ⥤ Stage C n :=
  relativeEvaluationStage C 1 n

/-- The actual quotient projection on all relative extension stages. -/
noncomputable def relativeQuotientStage (n : ℕ) :
    letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C;
    Stage (CofiberSequenceCategory C) n ⥤ Stage C n :=
  relativeEvaluationStage C 2 n

private theorem relativeEvaluationStage_obj_aux (k : Fin 3) (n : ℕ)
    (X : (letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C; Stage (CofiberSequenceCategory C) n)) :
    (letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C;
      (SConstruction.forget C n).obj ((relativeEvaluationStage C k n).obj X)) =
        X.obj ⋙ ((forget C) ⋙ (evaluation (Fin 3) C).obj k) := by
  let : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) := relativeWaldhausenCategory C
  unfold relativeEvaluationStage
  exact (evaluationIsRelativeWaldhausenExact C k).mapStage_obj n X

/-- The stage object is the original diagram followed by the original
row evaluation. -/
theorem relativeEvaluationStage_obj (k : Fin 3) (n : ℕ)
    (X : (letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C; Stage (CofiberSequenceCategory C) n)) :
    (letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C;
      (SConstruction.forget C n).obj ((relativeEvaluationStage C k n).obj X)) =
        X.obj ⋙ ((forget C) ⋙ (evaluation (Fin 3) C).obj k) :=
  relativeEvaluationStage_obj_aux C k n X

private theorem relativeEvaluationStage_map_aux (k : Fin 3) (n : ℕ)
    {X Y : (letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C; Stage (CofiberSequenceCategory C) n)} (φ : X ⟶ Y) :
    (letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C;
      (SConstruction.forget C n).map ((relativeEvaluationStage C k n).map φ)) =
        Functor.whiskerRight φ.hom ((forget C) ⋙ (evaluation (Fin 3) C).obj k) := by
  let : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) := relativeWaldhausenCategory C
  unfold relativeEvaluationStage
  exact (evaluationIsRelativeWaldhausenExact C k).mapStage_map n φ

private theorem relativeEvaluationStage_map_transport_aux (k : Fin 3) (n : ℕ)
    {X Y : (letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C; Stage (CofiberSequenceCategory C) n)} (φ : X ⟶ Y) :
    (letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C;
      (SConstruction.forget C n).map ((relativeEvaluationStage C k n).map φ)) =
        eqToHom (relativeEvaluationStage_obj C k n X) ≫
          Functor.whiskerRight φ.hom ((forget C) ⋙ (evaluation (Fin 3) C).obj k) ≫
          eqToHom (relativeEvaluationStage_obj C k n Y).symm := by
  let : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) := relativeWaldhausenCategory C
  exact (conj_eqToHom_iff_heq _ _
    (relativeEvaluationStage_obj C k n X)
    (relativeEvaluationStage_obj C k n Y)).2
      (heq_of_eq (relativeEvaluationStage_map_aux C k n φ))

/-- The stage morphism is the original postwhiskered diagram map,
transported through the proved source and target object computations. -/
theorem relativeEvaluationStage_map (k : Fin 3) (n : ℕ)
    {X Y : (letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C; Stage (CofiberSequenceCategory C) n)} (φ : X ⟶ Y) :
    (letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C;
      (SConstruction.forget C n).map ((relativeEvaluationStage C k n).map φ)) =
        eqToHom (relativeEvaluationStage_obj C k n X) ≫
          Functor.whiskerRight φ.hom ((forget C) ⋙ (evaluation (Fin 3) C).obj k) ≫
          eqToHom (relativeEvaluationStage_obj C k n Y).symm :=
  relativeEvaluationStage_map_transport_aux C k n φ

private theorem relativeEvaluationStage_forget_aux (k : Fin 3) (n : ℕ) :
    (letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C;
      relativeEvaluationStage C k n ⋙ SConstruction.forget C n =
        SConstruction.forget (CofiberSequenceCategory C) n ⋙
          (Functor.whiskeringRight (Ar n) (CofiberSequenceCategory C) C).obj
            ((forget C) ⋙ (evaluation (Fin 3) C).obj k)) := by
  let : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) := relativeWaldhausenCategory C
  apply Functor.hext
  · intro X
    exact relativeEvaluationStage_obj_aux C k n X
  · intro X Y φ
    apply heq_of_eq
    exact relativeEvaluationStage_map_aux C k n φ

/-- The whole stage functor computes to the original forgetful functor
followed by postcomposition with the original row evaluation. -/
theorem relativeEvaluationStage_forget (k : Fin 3) (n : ℕ) :
    (letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C;
      relativeEvaluationStage C k n ⋙ SConstruction.forget C n =
        SConstruction.forget (CofiberSequenceCategory C) n ⋙
          (Functor.whiskeringRight (Ar n) (CofiberSequenceCategory C) C).obj
            ((forget C) ⋙ (evaluation (Fin 3) C).obj k)) :=
  relativeEvaluationStage_forget_aux C k n

private theorem relativeEvaluationWeakStage_inclusion_aux (k : Fin 3) (n : ℕ) :
    (letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C;
      relativeEvaluationWeakStage C k n ⋙ stageWeakInclusion C n =
        stageWeakInclusion (CofiberSequenceCategory C) n ⋙ relativeEvaluationStage C k n) := by
  let : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) := relativeWaldhausenCategory C
  unfold relativeEvaluationWeakStage relativeEvaluationStage
  exact (evaluationIsRelativeWaldhausenExact C k).mapStageWeak_inclusion n

/-- Weak-stage restriction commutes with the actual weak-stage inclusions. -/
theorem relativeEvaluationWeakStage_inclusion (k : Fin 3) (n : ℕ) :
    (letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C;
      relativeEvaluationWeakStage C k n ⋙ stageWeakInclusion C n =
        stageWeakInclusion (CofiberSequenceCategory C) n ⋙ relativeEvaluationStage C k n) :=
  relativeEvaluationWeakStage_inclusion_aux C k n

private theorem relativeEvaluationStage_reindex_aux (k : Fin 3)
    {a b : SimplexCategory} (f : a ⟶ b) :
    (letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C;
      reindexStage (C := CofiberSequenceCategory C) f ⋙ relativeEvaluationStage C k a.len =
        relativeEvaluationStage C k b.len ⋙ reindexStage (C := C) f) := by
  let : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) := relativeWaldhausenCategory C
  unfold relativeEvaluationStage
  exact (evaluationIsRelativeWaldhausenExact C k).mapStage_reindex f

/-- Every original row evaluation commutes strictly with arbitrary
contravariant simplex reindexing of the genuine relative stages. -/
theorem relativeEvaluationStage_reindex (k : Fin 3)
    {a b : SimplexCategory} (f : a ⟶ b) :
    (letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C;
      reindexStage (C := CofiberSequenceCategory C) f ⋙ relativeEvaluationStage C k a.len =
        relativeEvaluationStage C k b.len ⋙ reindexStage (C := C) f) :=
  relativeEvaluationStage_reindex_aux C k f

private theorem relativeEvaluationWeakStage_reindex_aux (k : Fin 3)
    {a b : SimplexCategory} (f : a ⟶ b) :
    (letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C;
      reindexStageWeak (CofiberSequenceCategory C) f ⋙
          relativeEvaluationWeakStage C k a.len =
        relativeEvaluationWeakStage C k b.len ⋙ reindexStageWeak C f) := by
  let : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) := relativeWaldhausenCategory C
  unfold relativeEvaluationWeakStage
  exact (evaluationIsRelativeWaldhausenExact C k).mapStageWeak_reindex f

/-- The corresponding three weak-stage projections also commute
strictly with arbitrary contravariant simplex reindexing. -/
theorem relativeEvaluationWeakStage_reindex (k : Fin 3)
    {a b : SimplexCategory} (f : a ⟶ b) :
    (letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C;
      reindexStageWeak (CofiberSequenceCategory C) f ⋙
          relativeEvaluationWeakStage C k a.len =
        relativeEvaluationWeakStage C k b.len ⋙ reindexStageWeak C f) :=
  relativeEvaluationWeakStage_reindex_aux C k f

private theorem relativeEvaluationWeakStage_eq_aux (k : Fin 3) (n : ℕ) :
    (letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C;
      relativeEvaluationWeakStage C k n =
        (evaluationIsRelativeWaldhausenExact C k).mapStageWeak n) := by
  let : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) := relativeWaldhausenCategory C
  unfold relativeEvaluationWeakStage
  rfl

/-- The ENTIRE original relative weak-stage evaluation is the SAME
original exact evaluation's stage functor, with every map retained. -/
theorem relativeEvaluationWeakStage_eq (k : Fin 3) (n : ℕ) :
    (letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C;
      relativeEvaluationWeakStage C k n =
        (evaluationIsRelativeWaldhausenExact C k).mapStageWeak n) :=
  relativeEvaluationWeakStage_eq_aux C k n

end CofiberSequenceCategory

end CategoryTheory.Waldhausen.SConstruction
