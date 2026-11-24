/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectScalarCategories
import MathlibExt.CategoryTheory.Category.RelativeGenerators

/-!
# Actual attaching data and normalized word carriers on the original labels

The data are the original two simplicial quivers, their componentwise
monomorphism and the supplied original attaching Hom maps. In each
scalar degree, words use actual original Hom segments and target letters
outside the attaching image. Domain letters reduce to the same supplied
original Hom simplices. No pushout or weak-filtration result is an input.
-/

noncomputable section
universe u
open CategoryTheory Opposite

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.RelativeAttachment
open RelativeWords

variable {O : Type u} (C : FixedObjects O)

/-- The actual original quiver inclusion and attaching Hom maps, with unchanged object labels. -/
structure Data where
  /-- The original attaching-domain quiver. -/
  domain : SimplicialQuiver.Data O
  /-- The original target quiver. -/
  target : SimplicialQuiver.Data O
  /-- The actual simplicial inclusion at every original pair. -/
  inclusion (x y : O) : domain.Hom x y ⟶ target.Hom x y
  /-- Its genuine componentwise monomorphism property. -/
  mono (x y : O) : Mono (inclusion x y)
  /-- The same original attaching Hom maps. -/
  attaching (x y : O) : domain.Hom x y ⟶ hom C x y

variable {C}

/-- The actual source and target Hom maps in the given scalar degree. -/
abbrev inclusionAt (T : Data C) (q : SimplexCategoryᵒᵖ) {x y : O}
    (a : (T.domain.Hom x y).obj q) : (T.target.Hom x y).obj q := (T.inclusion x y).app q a

/-- The original attaching-domain Hom simplex is read in the same original scalar category. -/
abbrev attachingAt (T : Data C) (q : SimplexCategoryᵒᵖ) {x y : O}
    (a : (T.domain.Hom x y).obj q) : (hom C x y).obj q := (T.attaching x y).app q a

/-- Every scalar inclusion is genuinely injective, from the original simplicial monomorphism. -/
theorem inclusionAt_injective (T : Data C) (q : SimplexCategoryᵒᵖ) (x y : O) :
    Function.Injective (@inclusionAt O C T q x y) := by
  let _ : Mono (T.inclusion x y) := T.mono x y
  exact injective_of_mono ((T.inclusion x y).app q)

/-- Actual target letters outside the attaching image at the same individual original labels. -/
abbrev newAt (T : Data C) (q : SimplexCategoryᵒᵖ) : O → O → Type u :=
  @RelativeGenerators.newGenerators O
    (fun x y => (T.domain.Hom x y).obj q) (fun x y => (T.target.Hom x y).obj q)
    (fun {x y} a => inclusionAt T q a)

/-- The actual normalized original word carrier in one scalar degree, including every loop pair. -/
abbrev WordAt (T : Data C) (q : SimplexCategoryᵒᵖ) (x y : O) : Type u :=
  @Word O (scalarCategory C q) (newAt T q) x y

/-- Reduce an actual attaching-domain letter and retain every genuinely new target letter. -/
def letter (T : Data C) (q : SimplexCategoryᵒᵖ) {x y : O}
    (b : (T.target.Hom x y).obj q) : WordAt T q x y :=
  @RelativeGenerators.reduce O (scalarCategory C q)
    (fun x y => (T.domain.Hom x y).obj q) (fun x y => (T.target.Hom x y).obj q)
    (fun {x y} a => inclusionAt T q a) (fun {x y} a => attachingAt T q a) x y b

/-- The same original attaching-domain image reduces to its actual supplied original Hom simplex. -/
theorem letter_image (T : Data C) (q : SimplexCategoryᵒᵖ) {x y : O}
    (a : (T.domain.Hom x y).obj q) :
    letter T q (inclusionAt T q a) =
      @Word.old O (scalarCategory C q) (newAt T q) x y (attachingAt T q a) :=
  @RelativeGenerators.reduce_image O (scalarCategory C q)
    (fun x y => (T.domain.Hom x y).obj q) (fun x y => (T.target.Hom x y).obj q)
    (fun {x y} a => inclusionAt T q a) (fun {x y} a => attachingAt T q a)
    (inclusionAt_injective T q) x y a

/-- An actual new target simplex is its same literal length-one generator. -/
theorem letter_new (T : Data C) (q : SimplexCategoryᵒᵖ) {x y : O} (g : newAt T q x y) :
    letter T q g.val = @generator O (scalarCategory C q) (newAt T q) x y g :=
  @RelativeGenerators.reduce_new O (scalarCategory C q)
    (fun x y => (T.domain.Hom x y).obj q) (fun x y => (T.target.Hom x y).obj q)
    (fun {x y} a => inclusionAt T q a) (fun {x y} a => attachingAt T q a) x y g

/-- The actual attaching-domain reduction gives a letter of length at most one. -/
theorem length_letter_le (T : Data C) (q : SimplexCategoryᵒᵖ) {x y : O}
    (b : (T.target.Hom x y).obj q) :
    @Word.length O (scalarCategory C q) (newAt T q) x y (letter T q b) ≤ 1 :=
  @RelativeGenerators.length_reduce_le O (scalarCategory C q)
    (fun x y => (T.domain.Hom x y).obj q) (fun x y => (T.target.Hom x y).obj q)
    (fun {x y} a => inclusionAt T q a) (fun {x y} a => attachingAt T q a) x y b

end CategoryTheory.SimplicialEnrichment.FixedObjects.RelativeAttachment
