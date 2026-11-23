/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.SInverseSTranslation
public import MathlibExt.CategoryTheory.Preadditive.Skeleton

/-!
# Skeleton classes of translation stabilizers

The skeleton class of a translation arrow's stabilizer is independent of
its raw representative. Identity arrows have zero stabilizer class, and
composition adds stabilizer classes. The object and morphism universes of
the additive category are independent.
-/

@[expose] public section
noncomputable section

open CategoryTheory Limits ZeroObject

universe u v

namespace CategoryTheory.SInverseS

variable (C : Type u) [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

/-- The representative-independent skeleton class of the stabilizer of a
quotient translation arrow. -/
def translationStabilizerClass {B T : Translation C} (f : B ⟶ T) : Skeleton C :=
  Quotient.lift (fun r : Translation.RawHom B T => toSkeleton r.stabilizer)
    (fun _ _ h => by
      obtain ⟨e, _⟩ := h
      exact congr_toSkeleton_of_iso e) f

/-- Compute the stabilizer class using any raw representative. -/
theorem translationStabilizerClass_mk {X Y : Translation C}
    (r : Translation.RawHom X Y) :
    translationStabilizerClass C (Translation.Hom.mk r) = toSkeleton r.stabilizer :=
  rfl

/-- Compute the invariant using the selected raw representative of the
quotient arrow. -/
theorem translationStabilizerClass_out {X Y : Translation C} (f : X ⟶ Y) :
    translationStabilizerClass C f = toSkeleton (Quotient.out f).stabilizer :=
  (congrArg (translationStabilizerClass C) (Quotient.out_eq f).symm).trans
    (translationStabilizerClass_mk C (Quotient.out f))

/-- The stabilizer class of an identity arrow is zero. -/
theorem translationStabilizerClass_id (B : Translation C) :
    translationStabilizerClass C (𝟙 B) = 0 :=
  Skeleton.toSkeleton_zero

/-- Stabilizer classes add under composition. -/
theorem translationStabilizerClass_comp
    {B T U : Translation C} (f : B ⟶ T) (g : T ⟶ U) :
    translationStabilizerClass C (f ≫ g) =
      translationStabilizerClass C f + translationStabilizerClass C g := by
  induction f using Quotient.inductionOn with
  | _ f =>
      induction g using Quotient.inductionOn with
      | _ g =>
        change toSkeleton (g.stabilizer ⊞ f.stabilizer) =
          toSkeleton f.stabilizer + toSkeleton g.stabilizer
        exact (Skeleton.toSkeleton_biprod g.stabilizer f.stabilizer).trans (add_comm _ _)

end CategoryTheory.SInverseS

end
