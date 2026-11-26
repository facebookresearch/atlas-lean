/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.RelativeWordOperators
import MathlibExt.CategoryTheory.Category.RelativeWordRelabel

/-!
# Actual raw word simplex operators with exact finite length

The original scalar operator acts on each old segment and each original
target letter. Raw letters remain raw letters, so every exact-length
stratum is preserved. Identity, composition and the same individual
source/target labels are retained without an operator outcome input.
-/

noncomputable section
universe u
open CategoryTheory Opposite

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.RelativeAttachment
open RelativeWords

variable {O : Type u} {C : FixedObjects O}

/-- The actual raw word carrier with every original target-quiver letter retained. -/
abbrev RawWordAt (T : Data C) (q : SimplexCategoryᵒᵖ) (x y : O) : Type u :=
  @Word O (scalarCategory C q) (fun x y => (T.target.Hom x y).obj q) x y

/-- The same original simplex map acts on every whole raw word. -/
def rawOperator (T : Data C) {q r : SimplexCategoryᵒᵖ} (f : q ⟶ r)
    {x y : O} (p : RawWordAt T q x y) : RawWordAt T r x y :=
  @relabel O (scalarCategory C q) (fun x y => (T.target.Hom x y).obj q)
    O (scalarCategory C r) (fun x y => (T.target.Hom x y).obj r)
    (scalarOperator C f) (fun {x y} a => (T.target.Hom x y).map f a) x y p

/-- Raw scalar operators act by the same original Hom simplex map on every old segment. -/
theorem rawOperator_old (T : Data C) {q r : SimplexCategoryᵒᵖ} (f : q ⟶ r)
    {x y : O} (a : (hom C x y).obj q) :
    rawOperator T f (@Word.old O (scalarCategory C q) (fun x y => (T.target.Hom x y).obj q) x y a) =
      @Word.old O (scalarCategory C r) (fun x y => (T.target.Hom x y).obj r) x y ((hom C x y).map f a) := rfl

/-- Raw scalar operators keep each old segment, mapped target letter and complete remaining word. -/
theorem rawOperator_cons (T : Data C) {q r : SimplexCategoryᵒᵖ} (f : q ⟶ r)
    {a x y b : O} (h : (hom C a x).obj q) (e : (T.target.Hom x y).obj q) (p : RawWordAt T q y b) :
    rawOperator T f (@Word.cons O (scalarCategory C q) (fun x y => (T.target.Hom x y).obj q) a x y b h e p) =
      @Word.cons O (scalarCategory C r) (fun x y => (T.target.Hom x y).obj r) a x y b
        ((hom C a x).map f h) ((T.target.Hom x y).map f e) (rawOperator T f p) :=
  @relabel_cons O (scalarCategory C q) (fun x y => (T.target.Hom x y).obj q)
    O (scalarCategory C r) (fun x y => (T.target.Hom x y).obj r)
    (scalarOperator C f) (fun {x y} e => (T.target.Hom x y).map f e) a x y b h e p

/-- Every original raw scalar operator preserves the exact finite word length. -/
theorem length_rawOperator (T : Data C) {q r : SimplexCategoryᵒᵖ} (f : q ⟶ r)
    {x y : O} (p : RawWordAt T q x y) :
    @Word.length O (scalarCategory C r) (fun x y => (T.target.Hom x y).obj r) x y (rawOperator T f p) =
      @Word.length O (scalarCategory C q) (fun x y => (T.target.Hom x y).obj q) x y p :=
  @length_relabel O (scalarCategory C q) (fun x y => (T.target.Hom x y).obj q)
    O (scalarCategory C r) (fun x y => (T.target.Hom x y).obj r)
    (scalarOperator C f) (fun {x y} e => (T.target.Hom x y).map f e) x y p

/-- The actual identity operator fixes each whole raw word. -/
theorem rawOperator_id (T : Data C) (q : SimplexCategoryᵒᵖ) {x y : O} (p : RawWordAt T q x y) :
    rawOperator T (𝟙 q) p = p := by
  induction p with
  | @old x y h =>
      rw [rawOperator_old]
      have hh := congrArg (fun f => f h) ((hom C x y).map_id q)
      change (hom C x y).map (𝟙 q) h = h at hh
      rw [hh]
  | @cons a x y b h e p ih =>
      rw [rawOperator_cons, ih]
      have hh := congrArg (fun f => f h) ((hom C a x).map_id q)
      have he := congrArg (fun f => f e) ((T.target.Hom x y).map_id q)
      change (hom C a x).map (𝟙 q) h = h at hh
      change (T.target.Hom x y).map (𝟙 q) e = e at he
      rw [hh, he]

/-- Consecutive actual raw scalar operators act by their same whole composite. -/
theorem rawOperator_operator (T : Data C) {q r s : SimplexCategoryᵒᵖ} (f : q ⟶ r) (g : r ⟶ s)
    {x y : O} (p : RawWordAt T q x y) : rawOperator T g (rawOperator T f p) = rawOperator T (f ≫ g) p := by
  induction p with
  | @old x y h =>
      rw [rawOperator_old, rawOperator_old, rawOperator_old]
      have hh := congrArg (fun f => f h) ((hom C x y).map_comp f g)
      change (hom C x y).map (f ≫ g) h = (hom C x y).map g ((hom C x y).map f h) at hh
      rw [← hh]
  | @cons a x y b h e p ih =>
      rw [rawOperator_cons, rawOperator_cons, rawOperator_cons, ih]
      have hh := congrArg (fun f => f h) ((hom C a x).map_comp f g)
      have he := congrArg (fun f => f e) ((T.target.Hom x y).map_comp f g)
      change (hom C a x).map (f ≫ g) h = (hom C a x).map g ((hom C a x).map f h) at hh
      change (T.target.Hom x y).map (f ≫ g) e =
        (T.target.Hom x y).map g ((T.target.Hom x y).map f e) at he
      rw [← hh, ← he]

end CategoryTheory.SimplicialEnrichment.FixedObjects.RelativeAttachment
