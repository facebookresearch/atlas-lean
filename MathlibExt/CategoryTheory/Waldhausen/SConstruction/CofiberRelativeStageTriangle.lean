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

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.CofiberRelativeStages
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageCofibration
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageTwoFunctor
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.Zero
public import Mathlib.CategoryTheory.Functor.Currying

/-!
# The genuine cofiber triangle of relative extension stages

The original three row evaluations act functorially in their `Fin 3`
index on every regular finite stage. The source-to-middle arrow has the
genuine successive zero-row corner cofibrations, and its quotient square
is a whole pushout through an actual zero stage. Both facts come from the
original relative E(C) stage and its cofiber rows.

The existing general `stageTwoFunctor` supplies the S₂ encoding. The row
triangle and this grid commute with arbitrary simplex reindexing. No weak
natural splitting or inverse from three component stages is asserted.
-/

public section

open CategoryTheory Limits
open scoped ZeroObject

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

namespace CofiberSequenceCategory

/-- The original evaluation maps give the regular source/middle/quotient
stage functors as one actual `Fin 3`-indexed functor. -/
noncomputable def stageEvaluationTriangle (n : ℕ) :
    letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C;
    Fin 3 ⥤ (Stage (CofiberSequenceCategory C) n ⥤ Stage C n) := by
  let : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) := relativeWaldhausenCategory C
  exact {
    obj := fun k => (evaluationIsRelativeWaldhausenExact C k).mapStage n
    map := fun {k l} r => {
      app := fun A => ObjectProperty.homMk
        (Functor.whiskerLeft A.obj
          (Functor.whiskerLeft (forget C) ((evaluation (Fin 3) C).map r)))
      naturality := fun A B φ => by
        apply ObjectProperty.hom_ext
        apply NatTrans.ext
        funext x
        change (φ.hom.app x).hom.app k ≫ (B.obj.obj x).obj.map r =
          (A.obj.obj x).obj.map r ≫ (φ.hom.app x).hom.app l
        exact ((φ.hom.app x).hom.naturality r).symm }
    map_id := fun k => by
      apply NatTrans.ext
      funext A
      apply ObjectProperty.hom_ext
      apply NatTrans.ext
      funext x
      change (A.obj.obj x).obj.map (𝟙 k) = 𝟙 ((A.obj.obj x).obj.obj k)
      exact (A.obj.obj x).obj.map_id k
    map_comp := fun {k l m} r s => by
      apply NatTrans.ext
      funext A
      apply ObjectProperty.hom_ext
      apply NatTrans.ext
      funext x
      change (A.obj.obj x).obj.map (r ≫ s) =
        (A.obj.obj x).obj.map r ≫ (A.obj.obj x).obj.map s
      exact (A.obj.obj x).obj.map_comp r s }

/-- The source-to-middle arrow of the actual regular stage triangle. -/
noncomputable def stageSourceToMiddle (n : ℕ) :
    letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C;
    (stageEvaluationTriangle C n).obj 0 ⟶ (stageEvaluationTriangle C n).obj 1 :=
  (stageEvaluationTriangle C n).map
    (homOfLE (show (0 : Fin 3) ≤ 1 from by decide))

/-- The middle-to-quotient arrow of the actual regular stage triangle. -/
noncomputable def stageMiddleToQuotient (n : ℕ) :
    letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C;
    (stageEvaluationTriangle C n).obj 1 ⟶ (stageEvaluationTriangle C n).obj 2 :=
  (stageEvaluationTriangle C n).map
    (homOfLE (show (1 : Fin 3) ≤ 2 from by decide))

private theorem stageSourceToMiddle_cofibration_aux (n : ℕ)
    (A : (letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C; Stage (CofiberSequenceCategory C) n)) :
    (letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C;
      stageCofibrations C n ((stageSourceToMiddle C n).app A)) := by
  let : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) := relativeWaldhausenCategory C
  unfold stageSourceToMiddle stageEvaluationTriangle stageCofibrations
  intro j
  let r := horiz (Fin.zero_le j.castSucc) j.castSucc_le_succ
  let f := A.obj.map r
  have hf : IsCofibration f :=
    (A.property.cofiber_triple (Fin.zero_le j.castSucc) j.castSucc_le_succ).1
  have hrel := (isCofibration_relativeWaldhausenCategory_iff C f).mp hf
  obtain ⟨_, P, inB, inA, d, hP, hinBd, hinAd, hd⟩ :=
    (mem_relativeCofibrations_raw_iff C f).mp hrel
  refine ⟨P, inA, inB, d, ?_, ?_, ?_, hd⟩
  · exact hP.flip
  · exact hinAd
  · exact hinBd

/-- The source-to-middle stage arrow is a genuine Sₙ cofibration: each
successive zero-row corner is the actual corner in the relative E(C) stage. -/
theorem stageSourceToMiddle_isCofibration (n : ℕ)
    (A : (letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C; Stage (CofiberSequenceCategory C) n)) :
    (letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C;
      stageCofibrations C n ((stageSourceToMiddle C n).app A)) :=
  stageSourceToMiddle_cofibration_aux C n A

private theorem stageTriangle_zeroPushout_aux (n : ℕ)
    (A : (letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C; Stage (CofiberSequenceCategory C) n)) :
    (letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C;
      ∃ (Z : Stage C n), IsZero Z ∧
        ∃ (z : ((stageEvaluationTriangle C n).obj 0).obj A ⟶ Z)
          (q : Z ⟶ ((stageEvaluationTriangle C n).obj 2).obj A),
          IsPushout z ((stageSourceToMiddle C n).app A) q
            ((stageMiddleToQuotient C n).app A)) := by
  let : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) := relativeWaldhausenCategory C
  let : HasZeroMorphisms C := (isZero_zero C).hasZeroMorphisms
  unfold stageSourceToMiddle stageMiddleToQuotient stageEvaluationTriangle
  let Z : Stage C n := ⟨zeroDiagram C n, isStage_zeroDiagram C n⟩
  have hZ : IsZero Z := by
    apply IsZero.of_full_of_faithful_of_isZero (SConstruction.forget C n)
    exact Functor.isZero _ (fun _ => isZero_zero C)
  refine ⟨Z, hZ, 0, 0, ?_⟩
  apply IsPushout.of_map_of_faithful (SConstruction.forget C n)
  apply IsPushout.of_forall_isPushout_app
  intro x
  change IsPushout (0 : (A.obj.obj x).obj.obj 0 ⟶ (0 : C))
    ((A.obj.obj x).obj.map' 0 1) (0 : (0 : C) ⟶ (A.obj.obj x).obj.obj 2)
    ((A.obj.obj x).obj.map' 1 2)
  obtain ⟨_, z, q, hP⟩ := (A.obj.obj x).property
  have hz : z = 0 := (isZero_zero C).eq_of_tgt _ _
  have hq : q = 0 := (isZero_zero C).eq_of_src _ _
  simpa only [hz, hq] using hP

/-- The actual stage triangle has a whole quotient pushout through an
actual zero stage, obtained from the original cofiber rows pointwise. -/
theorem stageTriangle_exists_zeroPushout (n : ℕ)
    (A : (letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C; Stage (CofiberSequenceCategory C) n)) :
    (letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C;
      ∃ (Z : Stage C n), IsZero Z ∧
        ∃ (z : ((stageEvaluationTriangle C n).obj 0).obj A ⟶ Z)
          (q : Z ⟶ ((stageEvaluationTriangle C n).obj 2).obj A),
          IsPushout z ((stageSourceToMiddle C n).app A) q
            ((stageMiddleToQuotient C n).app A)) :=
  stageTriangle_zeroPushout_aux C n A

/-- The actual `Fin 3` parameterized stage functor of the cofiber triangle. -/
noncomputable def stageTriangleParameter (n : ℕ) :
    letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C;
    Stage (CofiberSequenceCategory C) n × Fin 3 ⥤ Stage C n := by
  let : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) := relativeWaldhausenCategory C
  exact Prod.swap (Stage (CofiberSequenceCategory C) n) (Fin 3) ⋙
    Functor.uncurry.obj (stageEvaluationTriangle C n)

private theorem stageTriangleParameter_reindex_aux
    {a b : SimplexCategory} (f : a ⟶ b) :
    (letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C;
      ((reindexStage (C := CofiberSequenceCategory C) f).prod (𝟭 (Fin 3))) ⋙
          stageTriangleParameter C a.len =
        stageTriangleParameter C b.len ⋙ reindexStage (C := C) f) := by
  let : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) := relativeWaldhausenCategory C
  unfold stageTriangleParameter stageEvaluationTriangle
  apply Functor.hext
  · intro X
    apply ObjectProperty.FullSubcategory.ext
    rfl
  · intro X Y φ
    apply heq_of_eq
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext x
    rfl

/-- The whole cofiber triangle parameter commutes with arbitrary simplex
reindexing, with coherence derived from the original diagrams. -/
theorem stageTriangleParameter_reindex
    {a b : SimplexCategory} (f : a ⟶ b) :
    (letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C;
      ((reindexStage (C := CofiberSequenceCategory C) f).prod (𝟭 (Fin 3))) ⋙
          stageTriangleParameter C a.len =
        stageTriangleParameter C b.len ⋙ reindexStage (C := C) f) :=
  stageTriangleParameter_reindex_aux C f

/-- The existing general S₂ functor encodes every original row of the
relative stage as an actual degree-two C-stage. -/
noncomputable def stageTriangleTwoGrid (n : ℕ) :
    letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C;
    Stage (CofiberSequenceCategory C) n ⥤ (Ar n ⥤ Stage C 2) := by
  let : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) := relativeWaldhausenCategory C
  exact SConstruction.forget (CofiberSequenceCategory C) n ⋙
    (Functor.whiskeringRight (Ar n) (CofiberSequenceCategory C) (Stage C 2)).obj
      (stageTwoFunctor C)

private theorem stageTriangleTwoGrid_obj_aux (n : ℕ)
    (A : (letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C; Stage (CofiberSequenceCategory C) n)) :
    (letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C;
      (stageTriangleTwoGrid C n).obj A) = A.obj ⋙ stageTwoFunctor C := by
  unfold stageTriangleTwoGrid
  rfl

/-- The S₂ grid is exactly postcomposition of the original diagram with
the existing degree-two cofiber functor. -/
theorem stageTriangleTwoGrid_obj (n : ℕ)
    (A : (letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C; Stage (CofiberSequenceCategory C) n)) :
    (letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C;
      (stageTriangleTwoGrid C n).obj A) = A.obj ⋙ stageTwoFunctor C :=
  stageTriangleTwoGrid_obj_aux C n A

private theorem stageEvaluationTriangle_obj_forget_aux (k : Fin 3) (n : ℕ)
    (A : (letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C;
      Stage (CofiberSequenceCategory C) n)) :
    (letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C;
      (SConstruction.forget C n).obj (((stageEvaluationTriangle C n).obj k).obj A)) =
        A.obj ⋙ ((forget C) ⋙ (evaluation (Fin 3) C).obj k) := by
  let : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) := relativeWaldhausenCategory C
  unfold stageEvaluationTriangle
  exact (evaluationIsRelativeWaldhausenExact C k).mapStage_obj n A

/-- Every original stage triangle object retains its whole original row
evaluation diagram after the original finite-stage forget functor. -/
theorem stageEvaluationTriangle_obj_forget (k : Fin 3) (n : ℕ)
    (A : (letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C;
      Stage (CofiberSequenceCategory C) n)) :
    (letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C;
      (SConstruction.forget C n).obj (((stageEvaluationTriangle C n).obj k).obj A)) =
        A.obj ⋙ ((forget C) ⋙ (evaluation (Fin 3) C).obj k) :=
  stageEvaluationTriangle_obj_forget_aux C k n A

private theorem stageEvaluationTriangle_map_forget_aux (k : Fin 3) (n : ℕ)
    {A B : (letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C;
      Stage (CofiberSequenceCategory C) n)} (φ : A ⟶ B) :
    (letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C;
      HEq ((SConstruction.forget C n).map (((stageEvaluationTriangle C n).obj k).map φ))
        (Functor.whiskerRight φ.hom ((forget C) ⋙ (evaluation (Fin 3) C).obj k))) := by
  let : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) := relativeWaldhausenCategory C
  unfold stageEvaluationTriangle
  apply heq_of_eq
  exact (evaluationIsRelativeWaldhausenExact C k).mapStage_map n φ

/-- Every original stage triangle morphism retains the original WHOLE
postwhiskered diagram morphism and its independently computed endpoint diagrams. -/
theorem stageEvaluationTriangle_map_forget (k : Fin 3) (n : ℕ)
    {A B : (letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C;
      Stage (CofiberSequenceCategory C) n)} (φ : A ⟶ B) :
    (letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C;
      HEq ((SConstruction.forget C n).map (((stageEvaluationTriangle C n).obj k).map φ))
        (Functor.whiskerRight φ.hom ((forget C) ⋙ (evaluation (Fin 3) C).obj k))) :=
  stageEvaluationTriangle_map_forget_aux C k n φ

/-- The whole first stage-triangle arrow retains the original source-to-middle
natural transformation with both original source and target diagrams. -/
theorem stageSourceToMiddle_app_hom (n : ℕ)
    (A : (letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C;
      Stage (CofiberSequenceCategory C) n)) :
    (letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C;
      HEq (((stageSourceToMiddle C n).app A).hom)
        (Functor.whiskerLeft A.obj (Functor.whiskerLeft (forget C)
          ((evaluation (Fin 3) C).map (homOfLE (show (0 : Fin 3) ≤ 1 from by decide)))))) := by
  let : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) := relativeWaldhausenCategory C
  unfold stageSourceToMiddle stageEvaluationTriangle
  rfl

/-- The whole second stage-triangle arrow retains the original middle-to-quotient
natural transformation with both original source and target diagrams. -/
theorem stageMiddleToQuotient_app_hom (n : ℕ)
    (A : (letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C;
      Stage (CofiberSequenceCategory C) n)) :
    (letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C;
      HEq (((stageMiddleToQuotient C n).app A).hom)
        (Functor.whiskerLeft A.obj (Functor.whiskerLeft (forget C)
          ((evaluation (Fin 3) C).map (homOfLE (show (1 : Fin 3) ≤ 2 from by decide)))))) := by
  let : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) := relativeWaldhausenCategory C
  unfold stageMiddleToQuotient stageEvaluationTriangle
  rfl


/-- Every whole original stage-triangle evaluation commutes with the
original simplex reindexing. This is the object law of the already proved
WHOLE triangle-parameter reindexing equality. -/
theorem stageEvaluationTriangle_obj_reindex {a b : SimplexCategory} (f : a ⟶ b)
    (A : (letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C;
      Stage (CofiberSequenceCategory C) b.len)) (k : Fin 3) :
    (letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C;
      ((stageEvaluationTriangle C a.len).obj k).obj
          ((reindexStage (C := CofiberSequenceCategory C) f).obj A) =
        (reindexStage (C := C) f).obj (((stageEvaluationTriangle C b.len).obj k).obj A)) := by
  let : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) := relativeWaldhausenCategory C
  exact Functor.congr_obj (stageTriangleParameter_reindex C f) (A, k)

/-- The WHOLE original source-middle stage arrow commutes with the
original simplex reindexing, retaining its independently evaluated endpoints. -/
theorem stageSourceToMiddle_app_reindex_hom {a b : SimplexCategory} (f : a ⟶ b)
    (A : (letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C;
      Stage (CofiberSequenceCategory C) b.len)) :
    (letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C;
      HEq (((reindexStage (C := C) f).map ((stageSourceToMiddle C b.len).app A)).hom)
        (((stageSourceToMiddle C a.len).app
          ((reindexStage (C := CofiberSequenceCategory C) f).obj A)).hom)) := by
  let : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) := relativeWaldhausenCategory C
  unfold stageSourceToMiddle stageEvaluationTriangle
  rfl

/-- The WHOLE original middle-quotient stage arrow commutes with the
original simplex reindexing, retaining the exact old quotient projection. -/
theorem stageMiddleToQuotient_app_reindex_hom {a b : SimplexCategory} (f : a ⟶ b)
    (A : (letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C;
      Stage (CofiberSequenceCategory C) b.len)) :
    (letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C;
      HEq (((reindexStage (C := C) f).map ((stageMiddleToQuotient C b.len).app A)).hom)
        (((stageMiddleToQuotient C a.len).app
          ((reindexStage (C := CofiberSequenceCategory C) f).obj A)).hom)) := by
  let : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) := relativeWaldhausenCategory C
  unfold stageMiddleToQuotient stageEvaluationTriangle
  rfl

end CofiberSequenceCategory

end CategoryTheory.Waldhausen.SConstruction
