/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.CategoryTheory.Monoidal.SInverseSSecondTranslationSpectralAction

/-!
# Actual class generators and commuting translation endomorphisms

These use the representation with only additive-category hypotheses. The
prescribed categorical composition order and independence of object
representatives remain visible to the consumer.
-/

open CategoryTheory Limits ZeroObject HomologicalComplex₂
open CategoryTheory.SInverseS

noncomputable section

variable {C : Type} [Category.{0} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] (R : AddCommGrpCat.{0})

example {A A' : C} (e : A ≅ A') :
    secondTranslationBKSpectralAction R (Multiplicative.ofAdd (toSkeleton A)) =
      secondTranslationBKSpectralAction R (Multiplicative.ofAdd (toSkeleton A')) := by
  rw [secondTranslationBKSpectralAction_toSkeleton,
    secondTranslationBKSpectralAction_toSkeleton]
  exact secondTranslationBKSpectralMap_eq_of_iso R e

example (A B : C) :
    (secondTranslationBKSpectralAction R (Multiplicative.ofAdd (toSkeleton (A ⊞ B)))).asHom =
      (secondTranslationBKSpectralMap R B).asHom ≫
        (secondTranslationBKSpectralMap R A).asHom := by
  rw [secondTranslationBKSpectralAction_toSkeleton,
    secondTranslationBKSpectralMap_biprod, End.mul_asHom]

example (A B : C) :
    Commute (secondTranslationBKSpectralMap R A) (secondTranslationBKSpectralMap R B) := by
  change secondTranslationBKSpectralMap R A * secondTranslationBKSpectralMap R B =
    secondTranslationBKSpectralMap R B * secondTranslationBKSpectralMap R A
  calc
    _ = secondTranslationBKSpectralMap R (A ⊞ B) :=
      (secondTranslationBKSpectralMap_biprod R A B).symm
    _ = secondTranslationBKSpectralMap R (B ⊞ A) :=
      secondTranslationBKSpectralMap_eq_of_iso R (biprod.braiding A B)
    _ = _ := secondTranslationBKSpectralMap_biprod R B A
