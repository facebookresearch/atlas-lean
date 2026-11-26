/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.RelativeRawWordOperators
import MathlibExt.AlgebraicTopology.SimplicialCategory.RelativeWordEnrichment
import MathlibExt.CategoryTheory.Category.RelativeWordNormalization

/-!
# The actual simplicial raw-word carrier and whole normalization map

Raw scalar operators retain each original target letter, while normalized
operators evaluate letters entering the attaching image. Whole original
normalization commutes with both actual operator actions and hence is a
genuine simplicial map. Forgetting normalized letters is only pointwise:
it is not asserted to commute with operators that lower word length.
-/

noncomputable section
universe u
open CategoryTheory Opposite

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.RelativeAttachment
open RelativeWords

variable {O : Type u} {C : FixedObjects O}

/-- The actual raw original word simplicial set at its same supplied source and target labels. -/
def rawWordHom (T : Data C) (x y : O) : SSet.{u} where
  obj q := RawWordAt T q x y
  map f := ↾fun p => rawOperator T f p
  map_id q := by ext p; exact rawOperator_id T q p
  map_comp f g := by ext p; exact (rawOperator_operator T f g p).symm

/-- Normalize the whole original raw word by the actual attaching Hom maps in its scalar degree. -/
def normalizeAt (T : Data C) (q : SimplexCategoryᵒᵖ) {x y : O} (p : RawWordAt T q x y) : WordAt T q x y :=
  @RelativeGenerators.normalize O (scalarCategory C q)
    (fun x y => (T.domain.Hom x y).obj q) (fun x y => (T.target.Hom x y).obj q)
    (fun {_ _} a => inclusionAt T q a) (fun {_ _} a => attachingAt T q a) x y p

/-- Whole normalization retains the same original length-zero Hom segment. -/
theorem normalizeAt_old (T : Data C) (q : SimplexCategoryᵒᵖ) {x y : O} (p : (hom C x y).obj q) :
    normalizeAt T q (@Word.old O (scalarCategory C q) (fun x y => (T.target.Hom x y).obj q) x y p) =
      oldWord T q p := rfl

/-- Whole normalization uses the same actual original segment, reduced target letter and remaining raw word. -/
theorem normalizeAt_cons (T : Data C) (q : SimplexCategoryᵒᵖ) {a x y b : O}
    (h : (hom C a x).obj q) (e : (T.target.Hom x y).obj q) (p : RawWordAt T q y b) :
    normalizeAt T q (@Word.cons O (scalarCategory C q) (fun x y => (T.target.Hom x y).obj q) a x y b h e p) =
      compWords T q (oldWord T q h) (compWords T q (letter T q e) (normalizeAt T q p)) := rfl

/-- The whole actual normalization commutes with every original scalar simplex operator. -/
theorem normalizeAt_operator (T : Data C) {q r : SimplexCategoryᵒᵖ} (f : q ⟶ r)
    {x y : O} (p : RawWordAt T q x y) :
    normalizeAt T r (rawOperator T f p) = operator T f (normalizeAt T q p) := by
  induction p with
  | @old x y h => rw [rawOperator_old, normalizeAt_old, normalizeAt_old, operator_old]
  | @cons a x y b h e p ih =>
      rw [rawOperator_cons, normalizeAt_cons, normalizeAt_cons, operator_comp, operator_old,
        operator_comp, operator_letter, ih]

/-- The entire actual raw-word normalization is a genuine simplicial Hom map. -/
def normalizationHom (T : Data C) (x y : O) : rawWordHom T x y ⟶ wordHom T x y where
  app q := ↾fun p => normalizeAt T q p
  naturality q r f := by ext p; exact normalizeAt_operator T f p

end CategoryTheory.SimplicialEnrichment.FixedObjects.RelativeAttachment
