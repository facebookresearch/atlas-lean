/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicTopology.SimplexCategory.Basic

/-!
# Actual proper ordinal images and their original refinement maps

The genuine categorical image of an original ordinal map is used with
its actual epi and mono factorization. A nonsurjective ordinal has a
strictly lower image degree. Every other original monic factorization
receives the actual image lift, with both whole equations retained.
No support colimit, matching or model outcome is assumed.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
namespace SimplexCategory

/-- An original monic nonsurjective ordinal map has strictly lower source degree. -/
theorem len_lt_of_mono_of_not_epi {A B : SimplexCategory} (f : A ⟶ B) [Mono f] (hf : ¬ Epi f) :
    A.len < B.len := by
  obtain ⟨m⟩ := A
  obtain ⟨n⟩ := B
  have hle : m ≤ n := len_le_of_mono f
  by_contra h
  change ¬ m < n at h
  have heq : m = n := by omega
  subst n
  apply hf
  rw [eq_id_of_mono f]
  infer_instance

/-- The SAME genuine original image of every nonsurjective ordinal lies in a strictly lower degree. -/
theorem image_len_lt_of_not_epi {A B : SimplexCategory} (f : A ⟶ B) (hf : ¬ Epi f) :
    (image f).len < B.len := by
  apply len_lt_of_mono_of_not_epi (image.ι f)
  intro h
  let _ : Epi (image.ι f) := h
  apply hf
  rw [← image.fac f]
  infer_instance

/-- Every supplied original monic ordinal factorization gives its actual full native factorization data. -/
def ordinalMonoFactorisation {A B P : SimplexCategory} (f : A ⟶ B)
    (m : P ⟶ B) [Mono m] (e : A ⟶ P) (he : e ≫ m = f) : MonoFactorisation f where
  I := P
  m := m
  e := e
  fac := he

/-- The actual original image lift to every other original monic ordinal factorization. -/
def ordinalImageLift {A B P : SimplexCategory} (f : A ⟶ B)
    (m : P ⟶ B) [Mono m] (e : A ⟶ P) (he : e ≫ m = f) : image f ⟶ P :=
  image.lift (ordinalMonoFactorisation f m e he)

/-- Its SAME full original target leg is exactly the genuine original image inclusion. -/
@[reassoc] theorem ordinalImageLift_target {A B P : SimplexCategory} (f : A ⟶ B)
    (m : P ⟶ B) [Mono m] (e : A ⟶ P) (he : e ≫ m = f) :
    ordinalImageLift f m e he ≫ m = image.ι f := image.lift_fac _

/-- Its SAME full original source leg is precisely the supplied original ordinal factor. -/
@[reassoc] theorem ordinalImageLift_source {A B P : SimplexCategory} (f : A ⟶ B)
    (m : P ⟶ B) [Mono m] (e : A ⟶ P) (he : e ≫ m = f) :
    factorThruImage f ≫ ordinalImageLift f m e he = e := image.fac_lift _

end SimplexCategory
