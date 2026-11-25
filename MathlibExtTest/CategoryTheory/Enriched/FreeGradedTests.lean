/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.FreeGraded
import Batteries.Tactic.Lint

/-!
# Importing the actual all-grade free/Lan generators

The generic clients retain independent plain index universes and the
original weighted coends for the left extension.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe uA uB uV vV u v
open CategoryTheory Limits MonoidalCategory EnrichedFunctorCat
open scoped MonoidalClosed

namespace FreeLanGradedOwner
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]

/-- An importing client constructs a full graded extension from a raw coefficient arrow. -/
def extension (Γ : Center V) (a : A) (M : V) (Y : EnrichedFunctorCat V A)
    (f : Γ.1 ⟶ (ihom M).obj (Y.toEnrichedFunctor.obj a)) :
    GradedNatTrans Γ (Free.object a M).toEnrichedFunctor Y.toEnrichedFunctor :=
  (FreeGraded.homEquiv Γ a M Y).symm f

example (Γ : Center V) (a : A) (M : V) (Y : EnrichedFunctorCat V A)
    (f : Γ.1 ⟶ (ihom M).obj (Y.toEnrichedFunctor.obj a)) (b c : A) :
    (Γ.2.β (b ⟶[V] c)).hom ≫
        ((Free.object a M).toEnrichedFunctor.map b c ⊗ₘ (extension Γ a M Y f).app c) ≫
        eComp V (M ⊗ (a ⟶[V] b)) (M ⊗ (a ⟶[V] c)) (Y.toEnrichedFunctor.obj c) =
      ((extension Γ a M Y f).app b ⊗ₘ Y.toEnrichedFunctor.map b c) ≫
        eComp V (M ⊗ (a ⟶[V] b)) (Y.toEnrichedFunctor.obj b) (Y.toEnrichedFunctor.obj c) :=
  (extension Γ a M Y f).naturality b c

example (Γ : Center V) (a : A) (M : V) (Y : EnrichedFunctorCat V A)
    (f : Γ.1 ⟶ (ihom M).obj (Y.toEnrichedFunctor.obj a)) (b : A) :
    GradedNatTrans.gradeFirstComponent Γ (extension Γ a M Y f) b =
      (α_ Γ.1 M (a ⟶[V] b)).inv ≫
        (((Γ.2.β M).hom ≫ MonoidalClosed.uncurry f) ▷ (a ⟶[V] b)) ≫
          MonoidalClosed.uncurry (Y.toEnrichedFunctor.map a b) :=
  FreeGraded.homEquiv_symm_gradeFirst Γ a M Y f b

example {Γ Δ : Center V} (h : Γ ⟶ Δ) (a : A) (M : V)
    (Y : EnrichedFunctorCat V A) (f : Δ.1 ⟶ (ihom M).obj (Y.toEnrichedFunctor.obj a)) :
    extension Γ a M Y (h.f ≫ f) = GradedNatTrans.regrade h (extension Δ a M Y f) :=
  FreeGraded.homEquiv_symm_regrade h a M Y f

example (Γ : Center V) (a : A) {M N : V} (f : M ⟶ N)
    (Y : EnrichedFunctorCat V A) (g : Γ.1 ⟶ (ihom N).obj (Y.toEnrichedFunctor.obj a)) :
    extension Γ a M Y (g ≫ (MonoidalClosed.pre f).app (Y.toEnrichedFunctor.obj a)) =
      gradedPrecomp Γ (Free.coefficientMap a f) (extension Γ a N Y g) :=
  FreeGraded.homEquiv_symm_coefficient Γ a f Y g

example (Γ : Center V) (a : A) (M : V) {Y Y' : EnrichedFunctorCat V A} (q : Y ⟶ Y')
    (f : Γ.1 ⟶ (ihom M).obj (Y.toEnrichedFunctor.obj a)) :
    extension Γ a M Y' (f ≫ (ihom M).map (component q a)) =
      gradedPostcomp Γ (extension Γ a M Y f) q :=
  FreeGraded.homEquiv_symm_postcomp Γ a M q f

example (a : A) (M : V) (Y : EnrichedFunctorCat V A) (K : Vᵒᵖ)
    (f : ULift.{max uA vV} (K.unop ⟶ (ihom M).obj (Y.toEnrichedFunctor.obj a))) :
    (FreeGraded.enrichedNatTransYonedaIso a M Y).inv.app K f =
      ULift.up (extension ((Center.ofBraided V).obj K.unop) a M Y f.down) :=
  FreeGraded.enrichedNatTransYonedaIso_inv_app a M Y K f

section Lan
variable {B : Type uB} [EnrichedCategory V B] (j : EnrichedFunctor V A B)
  [∀ (X : EnrichedFunctorCat V A) (b : B),
    HasCoproduct (Enriched.weightedCoend.relations (leftKanWeight j b) X.toEnrichedFunctor)]
  [∀ (X : EnrichedFunctorCat V A) (b : B),
    HasCoproduct (Enriched.weightedCoend.objects (leftKanWeight j b) X.toEnrichedFunctor)]
  [∀ (X : EnrichedFunctorCat V A) (b : B),
    HasCoequalizer (Enriched.weightedCoend.leftMap (leftKanWeight j b) X.toEnrichedFunctor)
      (Enriched.weightedCoend.rightMap (leftKanWeight j b) X.toEnrichedFunctor)]

/-- An importing client descends through the actual original j-weighted coends. -/
def lanExtension (Γ : Center V) (a : A) (M : V) (Y : EnrichedFunctorCat V B)
    (f : Γ.1 ⟶ (ihom M).obj (Y.toEnrichedFunctor.obj (j.obj a))) :
    GradedNatTrans Γ (leftKanObject j (Free.object a M)).toEnrichedFunctor
      Y.toEnrichedFunctor := (FreeGraded.lanHomEquiv j Γ a M Y).symm f

example (Γ : Center V) (a : A) (M : V) (Y : EnrichedFunctorCat V B)
    (f : Γ.1 ⟶ (ihom M).obj (Y.toEnrichedFunctor.obj (j.obj a))) (b : B) (a' : A) :
    (Γ.1 ◁ Enriched.weightedCoend.ι (leftKanWeight j b) (Free.object a M).toEnrichedFunctor a') ≫
      GradedNatTrans.gradeFirstComponent Γ (lanExtension j Γ a M Y f) b =
        FreeGraded.lanGenerator j Γ a M Y f b a' :=
  FreeGraded.lanHomEquiv_symm_generator j Γ a M Y f b a'

example (Γ : Center V) (a : A) (M : V) (Y : EnrichedFunctorCat V B)
    (t : GradedNatTrans Γ (leftKanObject j (Free.object a M)).toEnrichedFunctor
      Y.toEnrichedFunctor) :
    FreeGraded.lanHomEquiv j Γ a M Y t = t.app (j.obj a) ≫
      (MonoidalClosed.pre (FreeGraded.identityInsertion a M ≫
        leftKanUnitComponent j (Free.object a M) a)).app (Y.toEnrichedFunctor.obj (j.obj a)) :=
  FreeGraded.lanHomEquiv_apply j Γ a M Y t

example (Γ : Center V) (a : A) {M N : V} (f : M ⟶ N) (Y : EnrichedFunctorCat V B)
    (g : Γ.1 ⟶ (ihom N).obj (Y.toEnrichedFunctor.obj (j.obj a))) :
    lanExtension j Γ a M Y
        (g ≫ (MonoidalClosed.pre f).app (Y.toEnrichedFunctor.obj (j.obj a))) =
      gradedPrecomp Γ ((leftKan j).map (Free.coefficientMap a f))
        (lanExtension j Γ a N Y g) :=
  FreeGraded.lanHomEquiv_symm_coefficient j Γ a f Y g

example (Γ : Center V) (a : A) (M : V) (Y : EnrichedFunctorCat V B)
    (f : Γ.1 ⟶ (ihom M).obj (Y.toEnrichedFunctor.obj (j.obj a)))
    (t : GradedNatTrans Γ (leftKanObject j (Free.object a M)).toEnrichedFunctor
      Y.toEnrichedFunctor)
    (h : ∀ (b : B) (a' : A),
      (Γ.1 ◁ Enriched.weightedCoend.ι (leftKanWeight j b) (Free.object a M).toEnrichedFunctor a') ≫
        GradedNatTrans.gradeFirstComponent Γ t b = FreeGraded.lanGenerator j Γ a M Y f b a') :
    t = lanExtension j Γ a M Y f :=
  FreeGraded.lanGenerator_unique j Γ a M Y f t h

example (a : A) (M : V) (Y : EnrichedFunctorCat V B) (K : Vᵒᵖ)
    (f : ULift.{max uA uB vV} (K.unop ⟶ (ihom M).obj (Y.toEnrichedFunctor.obj (j.obj a)))) :
    (FreeGraded.lanEnrichedNatTransYonedaIso j a M Y).inv.app K f =
      ULift.up (lanExtension j ((Center.ofBraided V).obj K.unop) a M Y f.down) :=
  FreeGraded.lanEnrichedNatTransYonedaIso_inv_app j a M Y K f

end Lan
end FreeLanGradedOwner



#check @CategoryTheory.EnrichedFunctorCat.FreeGraded.identityInsertion
#check @CategoryTheory.EnrichedFunctorCat.FreeGraded.evaluationEquiv
#check @CategoryTheory.EnrichedFunctorCat.FreeGraded.evaluationEquiv_apply
#check @CategoryTheory.EnrichedFunctorCat.FreeGraded.evaluationEquiv_gradeFirst
#check @CategoryTheory.EnrichedFunctorCat.FreeGraded.evaluationEquiv_symm_apply
#check @CategoryTheory.EnrichedFunctorCat.FreeGraded.evaluationEquiv_symm_gradeFirst
#check @CategoryTheory.EnrichedFunctorCat.FreeGraded.evaluationEquiv_symm_app
#check @CategoryTheory.EnrichedFunctorCat.FreeGraded.evaluationEquiv_left_inverse
#check @CategoryTheory.EnrichedFunctorCat.FreeGraded.evaluationEquiv_right_inverse
#check @CategoryTheory.EnrichedFunctorCat.FreeGraded.homEquiv
#check @CategoryTheory.EnrichedFunctorCat.FreeGraded.homEquiv_factor
#check @CategoryTheory.EnrichedFunctorCat.FreeGraded.homEquiv_apply
#check @CategoryTheory.EnrichedFunctorCat.FreeGraded.homEquiv_symm_factor
#check @CategoryTheory.EnrichedFunctorCat.FreeGraded.homEquiv_symm_gradeFirst
#check @CategoryTheory.EnrichedFunctorCat.FreeGraded.homEquiv_coefficient
#check @CategoryTheory.EnrichedFunctorCat.FreeGraded.homEquiv_postcomp
#check @CategoryTheory.EnrichedFunctorCat.FreeGraded.homEquiv_regrade
#check @CategoryTheory.EnrichedFunctorCat.FreeGraded.homEquiv_symm_coefficient
#check @CategoryTheory.EnrichedFunctorCat.FreeGraded.homEquiv_symm_postcomp
#check @CategoryTheory.EnrichedFunctorCat.FreeGraded.homEquiv_symm_regrade
#check @CategoryTheory.EnrichedFunctorCat.FreeGraded.homEquiv_left_inverse
#check @CategoryTheory.EnrichedFunctorCat.FreeGraded.homEquiv_right_inverse
#check @CategoryTheory.EnrichedFunctorCat.FreeGraded.homEquiv_presheaf_naturality
#check @CategoryTheory.EnrichedFunctorCat.FreeGraded.enrichedNatTransYonedaIso
#check @CategoryTheory.EnrichedFunctorCat.FreeGraded.enrichedNatTransYonedaIso_hom_app
#check @CategoryTheory.EnrichedFunctorCat.FreeGraded.enrichedNatTransYonedaIso_inv_app
#check @CategoryTheory.EnrichedFunctorCat.FreeGraded.lanGenerator
#check @CategoryTheory.EnrichedFunctorCat.FreeGraded.lanHomEquiv
#check @CategoryTheory.EnrichedFunctorCat.FreeGraded.lanHomEquiv_apply
#check @CategoryTheory.EnrichedFunctorCat.FreeGraded.lanHomEquiv_symm_apply
#check @CategoryTheory.EnrichedFunctorCat.FreeGraded.lanHomEquiv_symm_generator
#check @CategoryTheory.EnrichedFunctorCat.FreeGraded.lanHomEquiv_left_inverse
#check @CategoryTheory.EnrichedFunctorCat.FreeGraded.lanHomEquiv_right_inverse
#check @CategoryTheory.EnrichedFunctorCat.FreeGraded.lanHomEquiv_regrade
#check @CategoryTheory.EnrichedFunctorCat.FreeGraded.lanHomEquiv_coefficient
#check @CategoryTheory.EnrichedFunctorCat.FreeGraded.lanHomEquiv_postcomp
#check @CategoryTheory.EnrichedFunctorCat.FreeGraded.lanHomEquiv_symm_regrade
#check @CategoryTheory.EnrichedFunctorCat.FreeGraded.lanHomEquiv_symm_coefficient
#check @CategoryTheory.EnrichedFunctorCat.FreeGraded.lanHomEquiv_symm_postcomp
#check @CategoryTheory.EnrichedFunctorCat.FreeGraded.lanHomEquiv_unique
#check @CategoryTheory.EnrichedFunctorCat.FreeGraded.lanGenerator_unique
#check @CategoryTheory.EnrichedFunctorCat.FreeGraded.lanHomEquiv_presheaf_naturality
#check @CategoryTheory.EnrichedFunctorCat.FreeGraded.lanEnrichedNatTransYonedaIso
#check @CategoryTheory.EnrichedFunctorCat.FreeGraded.lanEnrichedNatTransYonedaIso_hom_app
#check @CategoryTheory.EnrichedFunctorCat.FreeGraded.lanEnrichedNatTransYonedaIso_inv_app

#print axioms CategoryTheory.EnrichedFunctorCat.FreeGraded.identityInsertion
#print axioms CategoryTheory.EnrichedFunctorCat.FreeGraded.evaluationEquiv
#print axioms CategoryTheory.EnrichedFunctorCat.FreeGraded.evaluationEquiv_apply
#print axioms CategoryTheory.EnrichedFunctorCat.FreeGraded.evaluationEquiv_gradeFirst
#print axioms CategoryTheory.EnrichedFunctorCat.FreeGraded.evaluationEquiv_symm_apply
#print axioms CategoryTheory.EnrichedFunctorCat.FreeGraded.evaluationEquiv_symm_gradeFirst
#print axioms CategoryTheory.EnrichedFunctorCat.FreeGraded.evaluationEquiv_symm_app
#print axioms CategoryTheory.EnrichedFunctorCat.FreeGraded.evaluationEquiv_left_inverse
#print axioms CategoryTheory.EnrichedFunctorCat.FreeGraded.evaluationEquiv_right_inverse
#print axioms CategoryTheory.EnrichedFunctorCat.FreeGraded.homEquiv
#print axioms CategoryTheory.EnrichedFunctorCat.FreeGraded.homEquiv_factor
#print axioms CategoryTheory.EnrichedFunctorCat.FreeGraded.homEquiv_apply
#print axioms CategoryTheory.EnrichedFunctorCat.FreeGraded.homEquiv_symm_factor
#print axioms CategoryTheory.EnrichedFunctorCat.FreeGraded.homEquiv_symm_gradeFirst
#print axioms CategoryTheory.EnrichedFunctorCat.FreeGraded.homEquiv_coefficient
#print axioms CategoryTheory.EnrichedFunctorCat.FreeGraded.homEquiv_postcomp
#print axioms CategoryTheory.EnrichedFunctorCat.FreeGraded.homEquiv_regrade
#print axioms CategoryTheory.EnrichedFunctorCat.FreeGraded.homEquiv_symm_coefficient
#print axioms CategoryTheory.EnrichedFunctorCat.FreeGraded.homEquiv_symm_postcomp
#print axioms CategoryTheory.EnrichedFunctorCat.FreeGraded.homEquiv_symm_regrade
#print axioms CategoryTheory.EnrichedFunctorCat.FreeGraded.homEquiv_left_inverse
#print axioms CategoryTheory.EnrichedFunctorCat.FreeGraded.homEquiv_right_inverse
#print axioms CategoryTheory.EnrichedFunctorCat.FreeGraded.homEquiv_presheaf_naturality
#print axioms CategoryTheory.EnrichedFunctorCat.FreeGraded.enrichedNatTransYonedaIso
#print axioms CategoryTheory.EnrichedFunctorCat.FreeGraded.enrichedNatTransYonedaIso_hom_app
#print axioms CategoryTheory.EnrichedFunctorCat.FreeGraded.enrichedNatTransYonedaIso_inv_app
#print axioms CategoryTheory.EnrichedFunctorCat.FreeGraded.lanGenerator
#print axioms CategoryTheory.EnrichedFunctorCat.FreeGraded.lanHomEquiv
#print axioms CategoryTheory.EnrichedFunctorCat.FreeGraded.lanHomEquiv_apply
#print axioms CategoryTheory.EnrichedFunctorCat.FreeGraded.lanHomEquiv_symm_apply
#print axioms CategoryTheory.EnrichedFunctorCat.FreeGraded.lanHomEquiv_symm_generator
#print axioms CategoryTheory.EnrichedFunctorCat.FreeGraded.lanHomEquiv_left_inverse
#print axioms CategoryTheory.EnrichedFunctorCat.FreeGraded.lanHomEquiv_right_inverse
#print axioms CategoryTheory.EnrichedFunctorCat.FreeGraded.lanHomEquiv_regrade
#print axioms CategoryTheory.EnrichedFunctorCat.FreeGraded.lanHomEquiv_coefficient
#print axioms CategoryTheory.EnrichedFunctorCat.FreeGraded.lanHomEquiv_postcomp
#print axioms CategoryTheory.EnrichedFunctorCat.FreeGraded.lanHomEquiv_symm_regrade
#print axioms CategoryTheory.EnrichedFunctorCat.FreeGraded.lanHomEquiv_symm_coefficient
#print axioms CategoryTheory.EnrichedFunctorCat.FreeGraded.lanHomEquiv_symm_postcomp
#print axioms CategoryTheory.EnrichedFunctorCat.FreeGraded.lanHomEquiv_unique
#print axioms CategoryTheory.EnrichedFunctorCat.FreeGraded.lanGenerator_unique
#print axioms CategoryTheory.EnrichedFunctorCat.FreeGraded.lanHomEquiv_presheaf_naturality
#print axioms CategoryTheory.EnrichedFunctorCat.FreeGraded.lanEnrichedNatTransYonedaIso
#print axioms CategoryTheory.EnrichedFunctorCat.FreeGraded.lanEnrichedNatTransYonedaIso_hom_app
#print axioms CategoryTheory.EnrichedFunctorCat.FreeGraded.lanEnrichedNatTransYonedaIso_inv_app

#lint only unusedArguments in MathlibExt.CategoryTheory.Enriched.FreeGraded
