/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.IteratedStageCanonicalZero
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.IteratedStageReindex

/-!
# Strict reindexing of the constructed iterated zero diagram

The actual tuple functor preserves the recursively constructed constant-zero
object. Head reindexing precomposes a constant diagram; the exact tail map
postcomposes that diagram. The original successor carrier equations and
strict inverse laws retain the same objects at each step.

This concerns the explicit constructed zero, whose isomorphism to the
existentially chosen zero remains separate.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe u v uD vD uE vE
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject

namespace CategoryTheory.Waldhausen.SConstruction

private theorem constantPostcomp_eq {D : Type uD} {E : Type uE}
    [Category.{vD} D] [Category.{vE} E] (n : ℕ) (Z : D) (F : D ⥤ E) :
    (Functor.const (Ar n)).obj Z ⋙ F = (Functor.const (Ar n)).obj (F.obj Z) :=
  Functor.ext_of_iso (Functor.constComp (Ar n) Z F) (fun _ => rfl) (by
    intro X
    simp only [Functor.constComp_hom_app, eqToHom_refl])

variable (C : Type (max u v)) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- The original one-fold carrier chart sends the constructed zero to the original constant-zero
stage. -/
theorem iteratedStageCanonicalZero_onefold_obj (n : ℕ) :
    (((iteratedStageNilEquivalence_exact C).1).mapStage n).obj
        ((iteratedStageConsEquivalence C n []).functor.obj
          (iteratedStageCanonicalZero C [n])) = generalStageZero C n := by
  apply ObjectProperty.FullSubcategory.ext
  rw [Functor.IsWaldhausenExact.mapStage_obj, iteratedStageCanonicalZero_cons_obj,
    generalStageZero_obj]
  change (Functor.const (Ar n)).obj (iteratedStageCanonicalZero C []) ⋙
    (iteratedStageNilEquivalence C).functor = (Functor.const (Ar n)).obj (0 : C)
  rw [constantPostcomp_eq]
  exact congrArg (Functor.const (Ar n)).obj (iteratedStageCanonicalZero_nil C)

/-- Every actual tuple operator preserves the same recursively constructed constant-zero object. -/
theorem reindexIteratedStage_canonicalZero {r : ℕ} {a b : StageSimplexTuple r}
    (α : a ⟶ b) :
    (reindexIteratedStage C α).obj (iteratedStageCanonicalZero C (stageTupleDegrees a)) =
      iteratedStageCanonicalZero C (stageTupleDegrees b) := by
  induction r with
  | zero =>
      have ha : a = b := Subsingleton.elim _ _
      subst b
      rw [reindexIteratedStage_zero]
      rfl
  | succ r ih =>
      let dA : Fin (r + 1) → ℕ := fun i => (a i).unop.len
      let dB : Fin (r + 1) → ℕ := fun i => (b i).unop.len
      let ea := iteratedStageOfFnSuccEquivalence C dA
      let eb := iteratedStageOfFnSuccEquivalence C dB
      let ZA := iteratedStageCanonicalZero C (stageTupleDegrees a)
      let ZB := iteratedStageCanonicalZero C (stageTupleDegrees b)
      have hstage :
          ((reindexIteratedStage_isWaldhausenExact C (fun i => α i.succ)).mapStage
            (b 0).unop.len).obj
            ((reindexStage (C := StageAtTuple C (fun i => a i.succ)) (α 0).unop).obj
              (ea.functor.obj ZA)) = eb.functor.obj ZB := by
        apply ObjectProperty.FullSubcategory.ext
        rw [Functor.IsWaldhausenExact.mapStage_obj]
        change (indexFunctor (α 0).unop ⋙ (ea.functor.obj ZA).obj) ⋙
          reindexIteratedStage C (fun i => α i.succ) = (eb.functor.obj ZB).obj
        dsimp only [ea, eb, ZA, ZB, dA, dB, stageTupleDegrees]
        rw [iteratedStageCanonicalZero_tuple_successor C (fun i => (a i).unop.len),
          iteratedStageCanonicalZero_tuple_successor C (fun i => (b i).unop.len)]
        change (Functor.const (Ar (b 0).unop.len)).obj
            (iteratedStageCanonicalZero C (stageTupleDegrees (fun i => a i.succ))) ⋙
          reindexIteratedStage C (fun i => α i.succ) = _
        rw [constantPostcomp_eq]
        exact congrArg (Functor.const (Ar (b 0).unop.len)).obj (ih (fun i => α i.succ))
      have h := congrArg eb.inverse.obj hstage
      have hinv := Functor.congr_obj
        (iteratedStageOfFnSuccEquivalence_functor_inverse C dB) ZB
      change eb.inverse.obj (eb.functor.obj ZB) = ZB at hinv
      rw [reindexIteratedStage_succ_obj]
      exact h.trans hinv

end CategoryTheory.Waldhausen.SConstruction
