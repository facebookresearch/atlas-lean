/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.LocalizedBaseChangeWeakEquivalence

/-!
# Original zero, pure and full Q-span pullback clients

The two zero spans retain their different apex and leg formulas. Local base
hypotheses suffice for the zero and pure maps. The composition and quotient
observations use the actual Q arrows, and the projective case derives its
original base hypotheses for every associative unital ring.
-/

public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalActionCategory
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory ZeroObject

universe u v uRing vModule

namespace MathlibExtTest.LocalizedBaseChangeWeakEquivalence

open AlgebraicKTheory AlgebraicKTheory.LocalizedBaseChange

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

attribute [local instance] ExtensionCategory.leftSumAction
attribute [local instance] FixedTargetExtension.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction
attribute [local instance] ExtensionCategory.localizedTarget_isFibered

/-- Each actual zero-span model and pullback uses only the given object's original base. -/
theorem original_zero_span_models_and_local_weakness (X : C)
    (hBaseX : TopCat.weakHomotopyEquivalences
      (terminal.from (SSet.toTop.obj
        (nerve (MonoidalActionCategory (Core C) (FixedTargetExtension C X)) :
          SSet.{max u v})))) :
    (ExtensionCategory.zeroMonoSpan X).apex = (0 : C) ∧
      (ExtensionCategory.zeroMonoSpan X).l = 𝟙 (0 : C) ∧
      (ExtensionCategory.zeroMonoSpan X).r = (0 : (0 : C) ⟶ X) ∧
      (ExtensionCategory.zeroEpiSpan X).apex = X ∧
      (ExtensionCategory.zeroEpiSpan X).l = (0 : X ⟶ (0 : C)) ∧
      (ExtensionCategory.zeroEpiSpan X).r = 𝟙 X ∧
      SSet.realizationWeakEquivalences (nerveMap (zeroMonoBaseChange X)) ∧
      SSet.realizationWeakEquivalences (nerveMap (zeroEpiBaseChange X)) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · exact zeroMonoBaseChangeNerveMap_mem_of_originalBases_conull X hBaseX
  · exact zeroEpiBaseChangeNerveMap_mem_of_originalBases_conull X hBaseX

/-- Both original zero-span triangles retain their pure-arrow direction and local endpoints. -/
theorem original_pure_triangles_and_endpoint_weakness {M X : C}
    (hBaseM : TopCat.weakHomotopyEquivalences
      (terminal.from (SSet.toTop.obj
        (nerve (MonoidalActionCategory (Core C) (FixedTargetExtension C M)) :
          SSet.{max u v}))))
    (hBaseX : TopCat.weakHomotopyEquivalences
      (terminal.from (SSet.toTop.obj
        (nerve (MonoidalActionCategory (Core C) (FixedTargetExtension C X)) :
          SSet.{max u v}))))
    (mu : M ⟶ X) (hmu : IsAdmissibleMono mu)
    (lambda : M ⟶ X) (hlambda : IsAdmissibleEpi lambda) :
    ExtensionCategory.zeroMonoHom M ≫ QuillenQ.pureMonoHom mu hmu =
        ExtensionCategory.zeroMonoHom X ∧
      ExtensionCategory.zeroEpiHom X ≫ QuillenQ.pureEpiHom lambda hlambda =
        ExtensionCategory.zeroEpiHom M ∧
      SSet.realizationWeakEquivalences
        (nerveMap (baseChangeFunctor (QuillenQ.pureMonoHom mu hmu))) ∧
      SSet.realizationWeakEquivalences
        (nerveMap (baseChangeFunctor (QuillenQ.pureEpiHom lambda hlambda))) := by
  exact ⟨QuillenQ.zeroMonoHom_pureMonoHom mu hmu,
    QuillenQ.zeroEpiHom_pureEpiHom lambda hlambda,
    pureMonoBaseChangeNerveMap_mem_of_originalBases_conull hBaseM hBaseX mu hmu,
    pureEpiBaseChangeNerveMap_mem_of_originalBases_conull hBaseM hBaseX lambda hlambda⟩

/-- Pure compositions and units are the original quotient-category identities. -/
theorem original_pure_composition_and_units {A B X : C}
    (mu : A ⟶ B) (nu : B ⟶ X)
    (hmu : IsAdmissibleMono mu) (hnu : IsAdmissibleMono nu)
    (rho : A ⟶ B) (lambda : B ⟶ X)
    (hrho : IsAdmissibleEpi rho) (hlambda : IsAdmissibleEpi lambda) :
    QuillenQ.pureMonoHom mu hmu ≫ QuillenQ.pureMonoHom nu hnu =
        QuillenQ.pureMonoHom (mu ≫ nu) (admissibleMono_comp.comp_mem mu nu hmu hnu) ∧
      QuillenQ.pureEpiHom lambda hlambda ≫ QuillenQ.pureEpiHom rho hrho =
        QuillenQ.pureEpiHom (rho ≫ lambda)
          (admissibleEpi_comp.comp_mem rho lambda hrho hlambda) ∧
      QuillenQ.pureMonoHom (𝟙 X) (IsAdmissibleMono.id X) =
        (𝟙 (⟨X⟩ : QuillenQ C)) ∧
      QuillenQ.pureEpiHom (𝟙 X) (IsAdmissibleEpi.id X) =
        (𝟙 (⟨X⟩ : QuillenQ C)) := by
  refine ⟨QuillenQ.pureMonoHom_comp mu nu hmu hnu,
    QuillenQ.pureEpiHom_comp rho lambda hrho hlambda, ?_, ?_⟩
  · change QuillenQ.mkHom (X := ⟨X⟩) (Y := ⟨X⟩)
      (Span.id (c := X) : QuillenSpan X X) = _
    exact AlgebraicKTheory.mkHom_id (⟨X⟩ : QuillenQ C)
  · change QuillenQ.mkHom (X := ⟨X⟩) (Y := ⟨X⟩)
      (Span.id (c := X) : QuillenSpan X X) = _
    exact AlgebraicKTheory.mkHom_id (⟨X⟩ : QuillenQ C)

/-- The actual representative factorization and every original Q arrow have the derived pullback. -/
theorem original_span_factorization_and_all_arrow_weakness
    (hBase : ∀ Z : C, TopCat.weakHomotopyEquivalences
      (terminal.from (SSet.toTop.obj
        (nerve (MonoidalActionCategory (Core C) (FixedTargetExtension C Z)) :
          SSet.{max u v}))))
    {X Y : C} (sigma : QuillenSpan X Y)
    (phi : (⟨X⟩ : QuillenQ C) ⟶ (⟨Y⟩ : QuillenQ C)) :
    QuillenQ.pureEpiHom sigma.l sigma.wl ≫ QuillenQ.pureMonoHom sigma.r sigma.wr =
        QuillenQ.mkHom (X := ⟨X⟩) (Y := ⟨Y⟩) sigma ∧
      SSet.realizationWeakEquivalences
        (nerveMap (baseChangeFunctor
          (QuillenQ.mkHom (X := ⟨X⟩) (Y := ⟨Y⟩) sigma))) ∧
      SSet.realizationWeakEquivalences (nerveMap (baseChangeFunctor phi)) := by
  exact ⟨QuillenQ.pureEpiHom_pureMonoHom sigma,
    baseChangeNerveMap_mem_of_originalBases_conull hBase
      (QuillenQ.mkHom (X := ⟨X⟩) (Y := ⟨Y⟩) sigma),
    baseChangeNerveMap_mem_of_originalBases_conull hBase phi⟩

/-- The projective all-span client derives its original base family from Ring alone. -/
theorem projective_original_bases_and_all_span_weakness
    {R : Type uRing} [Ring R]
    {A B : QuillenQ (FGProjectiveCat.{vModule} R)} (phi : A ⟶ B) :
    (∀ X : FGProjectiveCat.{vModule} R, TopCat.weakHomotopyEquivalences
      (terminal.from (SSet.toTop.obj
        (nerve (MonoidalActionCategory (Core (FGProjectiveCat.{vModule} R))
          (FixedTargetExtension (FGProjectiveCat.{vModule} R) X)) :
            SSet.{max uRing (vModule + 1)})))) ∧
      SSet.realizationWeakEquivalences
        (nerveMap (baseChangeFunctor (C := FGProjectiveCat.{vModule} R) phi)) := by
  refine ⟨?_, projectiveBaseChangeNerveMap_mem_realizationWeakEquivalences phi⟩
  intro X
  exact AuxiliaryExtension.projectiveAuxiliary_realization_conull X

end MathlibExtTest.LocalizedBaseChangeWeakEquivalence

namespace AlgebraicKTheory.LocalizedBaseChange

#print axioms zeroMonoBaseChangeNerveMap_mem_of_originalBases_conull
#print axioms zeroEpiBaseChangeNerveMap_mem_of_originalBases_conull
#print axioms pureMonoBaseChangeNerveMap_mem_of_originalBases_conull
#print axioms pureEpiBaseChangeNerveMap_mem_of_originalBases_conull
#print axioms baseChangeNerveMap_mem_of_originalBases_conull
#print axioms projectiveBaseChangeNerveMap_mem_realizationWeakEquivalences

end AlgebraicKTheory.LocalizedBaseChange

namespace MathlibExtTest.LocalizedBaseChangeWeakEquivalence

#print axioms original_zero_span_models_and_local_weakness
#print axioms original_pure_triangles_and_endpoint_weakness
#print axioms original_pure_composition_and_units
#print axioms original_span_factorization_and_all_arrow_weakness
#print axioms projective_original_bases_and_all_span_weakness

end MathlibExtTest.LocalizedBaseChangeWeakEquivalence

end
