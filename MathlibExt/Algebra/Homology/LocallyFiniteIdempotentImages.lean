/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Abelian.IdempotentImageSplits
public import MathlibExt.Algebra.Homology.LocallyFiniteSplitComplex
public import MathlibExt.Algebra.Homology.LocallyFiniteSplitHomology

/-!
# Actual locally finite chain-idempotent image decompositions

The image object, inclusion and factor are the original native image
factorization of each original chain endomorphism. Actual orthogonality
splits those images and kills cross-image factors. Original finite support
and finite completeness in each chain degree give the actual complex and
homology coproduct inverses via native split-complex lemmas. No desired
complex/Hodge isomorphism, homology preservation, or global AB5 certificate
is supplied.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators

universe u v w

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Abelian C]
  [HasColimitsOfShape (Discrete ℕ) C]
  {ι : Type w} {c : ComplexShape ι}
  (K : HomologicalComplex C c) (e : ℕ → (K ⟶ K))
  (he : ∀ i j : ℕ, e i ≫ e j = if i = j then e i else 0)
  (N : ι → ℕ)
  (hsupport : ∀ n : ι, ∀ j : ℕ, N n < j → (e j).f n = 0)
  (hsum : ∀ n : ι, (∑ j : Fin (N n + 1), (e j.val).f n) = 𝟙 (K.X n))

include he in
omit [HasColimitsOfShape (Discrete ℕ) C] in
/-- The native image factor and inclusion split each actual idempotent. -/
theorem idempotentImage_split (j : ℕ) :
    image.ι (e j) ≫ factorThruImage (e j) = 𝟙 (image (e j)) :=
  image_ι_factorThruImage_of_idempotent (e j) ((he j j).trans (ite_eq_left (rfl : j = j)))

include he in
omit [HasColimitsOfShape (Discrete ℕ) C] in
/-- Orthogonality annihilates the factor between two distinct native idempotent images. -/
theorem idempotentImage_cross (j k : ℕ) (hjk : j ≠ k) :
    image.ι (e j) ≫ factorThruImage (e k) = 0 :=
  image_ι_factorThruImage_of_comp_zero (e j) (e k) ((he j k).trans (ite_eq_right hjk))

include hsupport in
omit [HasColimitsOfShape (Discrete ℕ) C] in
/-- A zero idempotent component makes the native image-factor component zero. -/
theorem idempotentImage_factor_support (n : ι) (j : ℕ) (hj : N n < j) :
    (factorThruImage (e j)).f n = 0 := by
  apply (cancel_mono ((image.ι (e j)).f n)).mp
  have h := congrArg (fun f => f.f n) (image.fac (e j))
  simpa only [HomologicalComplex.comp_f, hsupport n j hj, zero_comp] using h

include hsum in
omit [HasColimitsOfShape (Discrete ℕ) C] in
/-- The original finite projector sum is retained by the native image factorization. -/
theorem idempotentImage_projector_sum (n : ι) :
    (∑ j : Fin (N n + 1), (factorThruImage (e j.val)).f n ≫ (image.ι (e j.val)).f n) =
      𝟙 (K.X n) := by
  simp only [← HomologicalComplex.comp_f, image.fac]
  exact hsum n

include he hsupport hsum in
/-- The original native idempotent image complexes have their actual locally finite coproduct isomorphism. -/
def locallyFiniteIdempotentImageComplexIso : (∐ (fun j : ℕ => image (e j))) ≅ K :=
  locallyFiniteSplitComplexCoproductIso K (fun j : ℕ => image (e j))
    (fun j => image.ι (e j)) (fun j => factorThruImage (e j))
    (idempotentImage_split K e he) (idempotentImage_cross K e he) N
    (idempotentImage_factor_support K e N hsupport)
    (idempotentImage_projector_sum K e N hsum)

include he hsupport hsum in
/-- The original image homologies have their actual finite-projection coproduct inverse in every degree. -/
def locallyFiniteIdempotentImageHomologyIso (n : ι) :
    (∐ (fun j : ℕ => (image (e j)).homology n)) ≅ K.homology n :=
  finiteSplitHomologyCoproductIso K (fun j : ℕ => image (e j))
    (fun j => image.ι (e j)) (fun j => factorThruImage (e j))
    (idempotentImage_split K e he) (idempotentImage_cross K e he) n (N n)
    (idempotentImage_factor_support K e N hsupport n)
    (idempotentImage_projector_sum K e N hsum n)

end HomologicalComplex
