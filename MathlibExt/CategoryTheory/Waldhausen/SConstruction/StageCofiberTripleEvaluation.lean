/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageTwoExtraction
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageZeroRowCofiberFunctorSequence

/-!
# Exact evaluation of the original cofiber triples

Every original ordered triple is selected by the original three-vertex
simplex operator and the existing degree-two extraction. Its exactness
uses the existing full zero-row cofiber functor-sequence certificate,
including its genuine corner and original base descent. All three
objects, both arrows and all original map coefficients are retained.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits
open scoped Simplicial ZeroObject

universe u v

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

private theorem stageTwoExtraction_eq_zeroRowLift :
    stageTwoExtraction C =
      StageZeroRowCofiber.lift C 2 (show (1 : Fin 3) ≤ 2 by decide) := by
  let F := stageTwoExtraction C
  let G := StageZeroRowCofiber.lift C 2 (show (1 : Fin 3) ≤ 2 by decide)
  have hobj (A : Stage C 2) : F.obj A = G.obj A := by
    apply ObjectProperty.FullSubcategory.ext
    have h₀ : (F.obj A).obj.obj' 0 = (G.obj A).obj.obj' 0 := rfl
    have h₁ : (F.obj A).obj.obj' 1 = (G.obj A).obj.obj' 1 := rfl
    have h₂ : (F.obj A).obj.obj' 2 = (G.obj A).obj.obj' 2 := rfl
    refine ComposableArrows.ext₂ h₀ h₁ h₂ ?_ ?_
    · change A.obj.map (horiz (show (0 : Fin 3) ≤ 1 by decide)
          (show (1 : Fin 3) ≤ 2 by decide)) =
        𝟙 _ ≫ A.obj.map (horiz (show (0 : Fin 3) ≤ 1 by decide)
          (show (1 : Fin 3) ≤ 2 by decide)) ≫ 𝟙 _
      simp
    · change A.obj.map (vert (show (0 : Fin 3) ≤ 1 by decide)
          (show (1 : Fin 3) ≤ 2 by decide)) =
        𝟙 _ ≫ A.obj.map (vert (show (0 : Fin 3) ≤ 1 by decide)
          (show (1 : Fin 3) ≤ 2 by decide)) ≫ 𝟙 _
      simp
  let e : F ≅ G := NatIso.ofComponents (fun A => eqToIso (hobj A)) (by
    intro A B φ
    apply ObjectProperty.hom_ext
    apply ComposableArrows.hom_ext₂
    · change (CofiberSequenceCategory.source C).map (F.map φ) ≫
          (CofiberSequenceCategory.source C).map (eqToHom (hobj B)) =
        (CofiberSequenceCategory.source C).map (eqToHom (hobj A)) ≫
          (CofiberSequenceCategory.source C).map (G.map φ)
      simp only [eqToHom_map]
      change φ.hom.app (interval (0 : Fin 3) 1 (by decide)) ≫ 𝟙 _ =
        𝟙 _ ≫ φ.hom.app (interval (0 : Fin 3) 1 (by decide))
      simp
    · change (CofiberSequenceCategory.middle C).map (F.map φ) ≫
          (CofiberSequenceCategory.middle C).map (eqToHom (hobj B)) =
        (CofiberSequenceCategory.middle C).map (eqToHom (hobj A)) ≫
          (CofiberSequenceCategory.middle C).map (G.map φ)
      simp only [eqToHom_map]
      change φ.hom.app (interval (0 : Fin 3) 2 (by decide)) ≫ 𝟙 _ =
        𝟙 _ ≫ φ.hom.app (interval (0 : Fin 3) 2 (by decide))
      simp
    · change (CofiberSequenceCategory.quotient C).map (F.map φ) ≫
          (CofiberSequenceCategory.quotient C).map (eqToHom (hobj B)) =
        (CofiberSequenceCategory.quotient C).map (eqToHom (hobj A)) ≫
          (CofiberSequenceCategory.quotient C).map (G.map φ)
      simp only [eqToHom_map]
      change φ.hom.app (interval (1 : Fin 3) 2 (by decide)) ≫ 𝟙 _ =
        𝟙 _ ≫ φ.hom.app (interval (1 : Fin 3) 2 (by decide))
      simp)
  exact Functor.ext_of_iso e hobj (fun _ => rfl)

/-- The original degree-two extraction is exact for the named stage and relative values. -/
theorem stageTwoExtraction_isWaldhausenExact :
    letI := generalStageHasZeroObject C 2;
    letI := generalStageWaldhausenCategory C 2;
    letI := CofiberSequenceCategory.relativeWaldhausenCategory C;
    (stageTwoExtraction C).IsWaldhausenExact := by
  let := generalStageHasZeroObject C 2
  let := generalStageWaldhausenCategory C 2
  let := CofiberSequenceCategory.relativeWaldhausenCategory C
  rw [stageTwoExtraction_eq_zeroRowLift C]
  exact StageZeroRowCofiber.lift_isWaldhausenExact C 2 (show (1 : Fin 3) ≤ 2 by decide)

/-- Select the same original ordered triple and extract its original cofiber row. -/
def stageCofiberTripleEvaluation (n : ℕ) {i j k : Fin (n + 1)}
    (hij : i ≤ j) (hjk : j ≤ k) :
    Stage C n ⥤ CofiberSequenceCategory C :=
  reindexStage (C := C) (SimplexCategory.mkOfLeComp i j k hij hjk) ⋙ stageTwoExtraction C

/-- Every original triple evaluation is exact, with both source suppliers already earned. -/
theorem stageCofiberTripleEvaluation_isWaldhausenExact (n : ℕ)
    {i j k : Fin (n + 1)} (hij : i ≤ j) (hjk : j ≤ k) :
    letI := generalStageHasZeroObject C n;
    letI := generalStageWaldhausenCategory C n;
    letI := CofiberSequenceCategory.relativeWaldhausenCategory C;
    (stageCofiberTripleEvaluation C n hij hjk).IsWaldhausenExact := by
  let := generalStageHasZeroObject C n
  let := generalStageWaldhausenCategory C n
  let := generalStageHasZeroObject C 2
  let := generalStageWaldhausenCategory C 2
  let := CofiberSequenceCategory.relativeWaldhausenCategory C
  exact (reindexStage_general_isWaldhausenExact C
    (SimplexCategory.mkOfLeComp i j k hij hjk)).comp (stageTwoExtraction_isWaldhausenExact C)

/-- The source object is the original first interval of the supplied triple. -/
theorem stageCofiberTripleEvaluation_obj_source (n : ℕ)
    {i j k : Fin (n + 1)} (hij : i ≤ j) (hjk : j ≤ k) (A : Stage C n) :
    ((stageCofiberTripleEvaluation C n hij hjk).obj A).obj.obj' 0 =
      A.obj.obj (interval i j hij) := by
  rfl

/-- The middle object is the original spanning interval of the supplied triple. -/
theorem stageCofiberTripleEvaluation_obj_middle (n : ℕ)
    {i j k : Fin (n + 1)} (hij : i ≤ j) (hjk : j ≤ k) (A : Stage C n) :
    ((stageCofiberTripleEvaluation C n hij hjk).obj A).obj.obj' 1 =
      A.obj.obj (interval i k (hij.trans hjk)) := by
  rfl

/-- The quotient object is the original last interval of the supplied triple. -/
theorem stageCofiberTripleEvaluation_obj_quotient (n : ℕ)
    {i j k : Fin (n + 1)} (hij : i ≤ j) (hjk : j ≤ k) (A : Stage C n) :
    ((stageCofiberTripleEvaluation C n hij hjk).obj A).obj.obj' 2 =
      A.obj.obj (interval j k hjk) := by
  rfl

/-- The first arrow is the supplied original horizontal inclusion. -/
theorem stageCofiberTripleEvaluation_firstArrow (n : ℕ)
    {i j k : Fin (n + 1)} (hij : i ≤ j) (hjk : j ≤ k) (A : Stage C n) :
    ((stageCofiberTripleEvaluation C n hij hjk).obj A).obj.map' 0 1 =
      A.obj.map (horiz hij hjk) := by
  rfl

/-- The second arrow is the supplied original vertical quotient. -/
theorem stageCofiberTripleEvaluation_secondArrow (n : ℕ)
    {i j k : Fin (n + 1)} (hij : i ≤ j) (hjk : j ≤ k) (A : Stage C n) :
    ((stageCofiberTripleEvaluation C n hij hjk).obj A).obj.map' 1 2 =
      A.obj.map (vert hij hjk) := by
  rfl

/-- The source map is the same original first-interval coefficient. -/
theorem stageCofiberTripleEvaluation_map_source (n : ℕ)
    {i j k : Fin (n + 1)} (hij : i ≤ j) (hjk : j ≤ k)
    {A B : Stage C n} (φ : A ⟶ B) :
    ((stageCofiberTripleEvaluation C n hij hjk).map φ).hom.app 0 =
      φ.hom.app (interval i j hij) := by
  rfl

/-- The middle map is the same original spanning-interval coefficient. -/
theorem stageCofiberTripleEvaluation_map_middle (n : ℕ)
    {i j k : Fin (n + 1)} (hij : i ≤ j) (hjk : j ≤ k)
    {A B : Stage C n} (φ : A ⟶ B) :
    ((stageCofiberTripleEvaluation C n hij hjk).map φ).hom.app 1 =
      φ.hom.app (interval i k (hij.trans hjk)) := by
  rfl

/-- The quotient map is the same original last-interval coefficient. -/
theorem stageCofiberTripleEvaluation_map_quotient (n : ℕ)
    {i j k : Fin (n + 1)} (hij : i ≤ j) (hjk : j ≤ k)
    {A B : Stage C n} (φ : A ⟶ B) :
    ((stageCofiberTripleEvaluation C n hij hjk).map φ).hom.app 2 =
      φ.hom.app (interval j k hjk) := by
  rfl

/-- The whole original source projection is the original first interval evaluation. -/
theorem stageCofiberTripleEvaluation_source (n : ℕ)
    {i j k : Fin (n + 1)} (hij : i ≤ j) (hjk : j ≤ k) :
    stageCofiberTripleEvaluation C n hij hjk ⋙ CofiberSequenceCategory.source C =
      eval C n (interval i j hij) := by
  rfl

/-- The whole original middle projection is the spanning interval evaluation. -/
theorem stageCofiberTripleEvaluation_middle (n : ℕ)
    {i j k : Fin (n + 1)} (hij : i ≤ j) (hjk : j ≤ k) :
    stageCofiberTripleEvaluation C n hij hjk ⋙ CofiberSequenceCategory.middle C =
      eval C n (interval i k (hij.trans hjk)) := by
  rfl

/-- The whole original quotient projection is the original last interval evaluation. -/
theorem stageCofiberTripleEvaluation_quotient (n : ℕ)
    {i j k : Fin (n + 1)} (hij : i ≤ j) (hjk : j ≤ k) :
    stageCofiberTripleEvaluation C n hij hjk ⋙ CofiberSequenceCategory.quotient C =
      eval C n (interval j k hjk) := by
  rfl

/-- Every original simplex operator retains the whole supplied cofiber-triple evaluation. -/
theorem stageCofiberTripleEvaluation_reindex {a b : SimplexCategory} (α : a ⟶ b)
    {i j k : Fin (a.len + 1)} (hij : i ≤ j) (hjk : j ≤ k) :
    reindexStage (C := C) α ⋙ stageCofiberTripleEvaluation C a.len hij hjk =
      stageCofiberTripleEvaluation C b.len
        (α.toOrderHom.monotone hij) (α.toOrderHom.monotone hjk) := by
  have h : SimplexCategory.mkOfLeComp i j k hij hjk ≫ α =
      SimplexCategory.mkOfLeComp (α.toOrderHom i) (α.toOrderHom j) (α.toOrderHom k)
        (α.toOrderHom.monotone hij) (α.toOrderHom.monotone hjk) := by
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext x
    fin_cases x <;> rfl
  unfold stageCofiberTripleEvaluation
  rw [← Functor.assoc, ← reindexStage_comp, h]

end CategoryTheory.Waldhausen.SConstruction

end

