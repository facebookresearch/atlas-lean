/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.RelativeAttachment
import MathlibExt.CategoryTheory.Category.RelativeGeneratorsNaturality

/-!
# Actual simplex operators on the normalized original words

Every original scalar operator acts on each old Hom segment and target
letter. A letter entering the attaching image is evaluated by the same
original attaching map. Actual reduction naturality proves the whole
letter equation; whole-word substitution gives composition and the
length-filtration bound, without a supplied simplicial or weak outcome.
-/

noncomputable section
universe u
open CategoryTheory Opposite

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.RelativeAttachment
open RelativeWords

variable {O : Type u} {C : FixedObjects O}

/-- The same original Hom simplex as a literal length-zero word. -/
abbrev oldWord (T : Data C) (q : SimplexCategoryᵒᵖ) {x y : O} (a : (hom C x y).obj q) :
    WordAt T q x y := @Word.old O (scalarCategory C q) (newAt T q) x y a

/-- Concatenate the actual normalized original words at their same supplied middle label. -/
abbrev compWords (T : Data C) (q : SimplexCategoryᵒᵖ) {x y z : O}
    (p : WordAt T q x y) (r : WordAt T q y z) : WordAt T q x z :=
  @Word.comp O (scalarCategory C q) (newAt T q) x y z p r

/-- The actual original segment, individual new letter and whole remaining word. -/
abbrev consWord (T : Data C) (q : SimplexCategoryᵒᵖ) {a x y b : O}
    (f : (hom C a x).obj q) (g : newAt T q x y) (p : WordAt T q y b) : WordAt T q a b :=
  @Word.cons O (scalarCategory C q) (newAt T q) a x y b f g p

/-- The actual scalar operator substitutes every original segment and target letter in the whole word. -/
def operator (T : Data C) {q r : SimplexCategoryᵒᵖ} (f : q ⟶ r)
    {x y : O} (p : WordAt T q x y) : WordAt T r x y :=
  @substitute O (scalarCategory C q) (newAt T q) O (scalarCategory C r) (newAt T r)
    (scalarOperator C f)
    (fun {x y} g => letter T r ((T.target.Hom x y).map f g.val)) x y p

/-- The actual operator reads every original Hom segment by its same original simplex map. -/
theorem operator_old (T : Data C) {q r : SimplexCategoryᵒᵖ} (f : q ⟶ r)
    {x y : O} (a : (hom C x y).obj q) :
    operator T f (oldWord T q a) = oldWord T r ((hom C x y).map f a) := rfl

/-- The whole original operator preserves actual word concatenation. -/
theorem operator_comp (T : Data C) {q r : SimplexCategoryᵒᵖ} (f : q ⟶ r)
    {x y z : O} (p : WordAt T q x y) (t : WordAt T q y z) :
    operator T f (compWords T q p t) = compWords T r (operator T f p) (operator T f t) :=
  @substitute_comp O (scalarCategory C q) (newAt T q) O (scalarCategory C r) (newAt T r)
    (scalarOperator C f) (fun {x y} g => letter T r ((T.target.Hom x y).map f g.val)) x y z p t

/-- Actual domain-image reduction commutes with every original scalar operator. -/
theorem operator_letter (T : Data C) {q r : SimplexCategoryᵒᵖ} (f : q ⟶ r)
    {x y : O} (b : (T.target.Hom x y).obj q) :
    operator T f (letter T q b) = letter T r ((T.target.Hom x y).map f b) :=
  @RelativeGenerators.reduce_naturality O (scalarCategory C q) O (scalarCategory C r)
    (fun x y => (T.domain.Hom x y).obj q) (fun x y => (T.target.Hom x y).obj q)
    (fun x y => (T.domain.Hom x y).obj r) (fun x y => (T.target.Hom x y).obj r)
    (scalarOperator C f)
    (fun {_ _} a => inclusionAt T q a) (fun {_ _} a => attachingAt T q a)
    (fun {_ _} a => inclusionAt T r a) (fun {_ _} a => attachingAt T r a)
    (fun {x y} a => (T.domain.Hom x y).map f a) (fun {x y} a => (T.target.Hom x y).map f a)
    (inclusionAt_injective T r)
    (fun {x y} a => congr($((T.inclusion x y).naturality f) a).symm)
    (fun {x y} a => congr($((T.attaching x y).naturality f) a).symm) x y b

/-- Every original simplex operator preserves the entire normalized word-length filtration. -/
theorem operator_length_le (T : Data C) {q r : SimplexCategoryᵒᵖ} (f : q ⟶ r)
    {x y : O} (p : WordAt T q x y) :
    @Word.length O (scalarCategory C r) (newAt T r) x y (operator T f p) ≤
      @Word.length O (scalarCategory C q) (newAt T q) x y p :=
  @length_substitute_le O (scalarCategory C q) (newAt T q) O (scalarCategory C r) (newAt T r)
    (scalarOperator C f) (fun {x y} g => letter T r ((T.target.Hom x y).map f g.val))
    (fun {x y} g => length_letter_le T r ((T.target.Hom x y).map f g.val)) x y p

/-- The same scalar operator keeps the original first segment and the complete remaining boundary. -/
theorem operator_cons (T : Data C) {q r : SimplexCategoryᵒᵖ} (f : q ⟶ r)
    {a x y b : O} (h : (hom C a x).obj q) (g : newAt T q x y) (p : WordAt T q y b) :
    operator T f (consWord T q h g p) =
      compWords T r (oldWord T r ((hom C a x).map f h))
        (compWords T r (letter T r ((T.target.Hom x y).map f g.val)) (operator T f p)) := rfl

/-- The identity simplex map fixes every whole original normalized word. -/
theorem operator_id (T : Data C) (q : SimplexCategoryᵒᵖ) {x y : O} (p : WordAt T q x y) :
    operator T (𝟙 q) p = p := by
  induction p with
  | @old x y h =>
      have hh := congrArg (fun f => f h) ((hom C x y).map_id q)
      exact congrArg (oldWord T q) hh
  | @cons a x y b h g p ih =>
      change operator T (𝟙 q) (consWord T q h g p) = consWord T q h g p
      rw [operator_cons, ih]
      have hh := congrArg (fun f => f h) ((hom C a x).map_id q)
      have hg := congrArg (fun f => f g.val) ((T.target.Hom x y).map_id q)
      change (hom C a x).map (𝟙 q) h = h at hh
      change (T.target.Hom x y).map (𝟙 q) g.val = g.val at hg
      rw [hh, hg, letter_new]
      exact (@Word.assoc O (scalarCategory C q) (newAt T q) _ _ _ _ _ _ _).symm.trans
        (@cons_eq_comp O (scalarCategory C q) (newAt T q) _ _ _ _ h g p).symm

/-- Consecutive original simplex operators act by their same entire composite on every word. -/
theorem operator_operator (T : Data C) {q r s : SimplexCategoryᵒᵖ} (f : q ⟶ r) (g : r ⟶ s)
    {x y : O} (p : WordAt T q x y) : operator T g (operator T f p) = operator T (f ≫ g) p := by
  induction p with
  | @old x y h =>
      rw [operator_old, operator_old, operator_old]
      exact congrArg (oldWord T s) (congrArg (fun m => m h) ((hom C x y).map_comp f g)).symm
  | @cons a x y b h e p ih =>
      change operator T g (operator T f (consWord T q h e p)) =
        operator T (f ≫ g) (consWord T q h e p)
      rw [operator_cons, operator_comp, operator_old, operator_comp, operator_letter,
        ih, operator_cons]
      have hh := congrArg (fun m => m h) ((hom C a x).map_comp f g)
      have he := congrArg (fun m => m e.val) ((T.target.Hom x y).map_comp f g)
      change (hom C a x).map (f ≫ g) h = (hom C a x).map g ((hom C a x).map f h) at hh
      change (T.target.Hom x y).map (f ≫ g) e.val =
        (T.target.Hom x y).map g ((T.target.Hom x y).map f e.val) at he
      rw [← hh, ← he]

end CategoryTheory.SimplicialEnrichment.FixedObjects.RelativeAttachment
