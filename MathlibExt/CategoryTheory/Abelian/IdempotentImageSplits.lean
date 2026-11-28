/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.CategoryTheory.Abelian.Images
public import Mathlib.CategoryTheory.Abelian.Basic

/-!
# Splitting idempotents through their images

The image factorization of an idempotent supplies a splitting through its
image. Cancellation of the image epimorphism and monomorphism proves both
retraction identities and the zero-composition law between image factors.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [CategoryTheory.Abelian C]

/-- The image inclusion and factor of the idempotent are an split pair. -/
@[reassoc]
theorem image_ι_factorThruImage_of_idempotent {X : C} (p : X ⟶ X) (hp : p ≫ p = p) :
    image.ι p ≫ factorThruImage p = 𝟙 (image p) := by
  apply (cancel_epi (factorThruImage p)).mp
  apply (cancel_mono (image.ι p)).mp
  simpa only [Category.assoc, image.fac_assoc, image.fac, Category.comp_id] using hp

/-- Orthogonal endomorphisms give zero composites between their images. -/
@[reassoc]
theorem image_ι_factorThruImage_of_comp_zero {X : C} (p q : X ⟶ X) (hpq : p ≫ q = 0) :
    image.ι p ≫ factorThruImage q = 0 := by
  apply (cancel_epi (factorThruImage p)).mp
  apply (cancel_mono (image.ι q)).mp
  simpa only [Category.assoc, image.fac_assoc, image.fac, comp_zero, zero_comp] using hpq

end CategoryTheory.Limits
