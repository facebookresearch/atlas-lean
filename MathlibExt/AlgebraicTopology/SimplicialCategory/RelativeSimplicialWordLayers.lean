/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.RelativeRawWordNormalization
import MathlibExt.CategoryTheory.Category.RelativeWordCountNaturality
import MathlibExt.CategoryTheory.Category.RelativeWordLayerPushout
import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex

/-!
# The actual simplicial original relative-word length layers

Normalized word length never increases under original scalar operators.
Raw word length is preserved exactly, and the actual new-letter count
does not increase. Thus the original normalized layers, exact raw strata
and raw attaching boundaries are genuine subcomplexes. Normalization
gives their actual simplicial maps, retaining every original label.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.RelativeAttachment
open RelativeWords

variable {O : Type u} {C : FixedObjects O}

/-- Count the actual target letters outside the attaching image in the same original scalar word. -/
abbrev countAt (T : Data C) (q : SimplexCategoryᵒᵖ) {x y : O} (p : RawWordAt T q x y) : ℕ :=
  @RelativeGenerators.count O (scalarCategory C q)
    (fun x y => (T.domain.Hom x y).obj q) (fun x y => (T.target.Hom x y).obj q)
    (fun {_ _} a => inclusionAt T q a) x y p

/-- Actual original raw scalar operators do not increase the whole attaching-image new-letter count. -/
theorem countAt_rawOperator_le (T : Data C) {q r : SimplexCategoryᵒᵖ} (f : q ⟶ r)
    {x y : O} (p : RawWordAt T q x y) : countAt T r (rawOperator T f p) ≤ countAt T q p :=
  @RelativeGenerators.count_relabel_le O (scalarCategory C q) O (scalarCategory C r)
    (fun x y => (T.domain.Hom x y).obj q) (fun x y => (T.target.Hom x y).obj q)
    (fun x y => (T.domain.Hom x y).obj r) (fun x y => (T.target.Hom x y).obj r)
    (scalarOperator C f) (fun {_ _} a => inclusionAt T q a) (fun {_ _} a => inclusionAt T r a)
    (fun {x y} a => (T.domain.Hom x y).map f a) (fun {x y} a => (T.target.Hom x y).map f a)
    (fun {x y} a => congr($((T.inclusion x y).naturality f) a).symm) x y p

/-- The normalized word length is exactly its actual original new-letter count. -/
theorem length_normalizeAt (T : Data C) (q : SimplexCategoryᵒᵖ) {x y : O} (p : RawWordAt T q x y) :
    @Word.length O (scalarCategory C q) (newAt T q) x y (normalizeAt T q p) = countAt T q p :=
  @RelativeGenerators.length_normalize_eq_count O (scalarCategory C q)
    (fun x y => (T.domain.Hom x y).obj q) (fun x y => (T.target.Hom x y).obj q)
    (fun {_ _} a => inclusionAt T q a) (fun {_ _} a => attachingAt T q a) x y p

/-- The actual normalized original word subcomplex with length at most n. -/
def layer (T : Data C) (x y : O) (n : ℕ) : (wordHom T x y).Subcomplex where
  obj q := {p | @Word.length O (scalarCategory C q) (newAt T q) x y p ≤ n}
  map f p hp := (operator_length_le T f p).trans hp

/-- The actual original raw word subcomplex with exactly n+1 target letters. -/
def rawLayer (T : Data C) (x y : O) (n : ℕ) : (rawWordHom T x y).Subcomplex where
  obj q := {p | @Word.length O (scalarCategory C q) (fun x y => (T.target.Hom x y).obj q) x y p = n + 1}
  map f p hp := (length_rawOperator T f p).trans hp

/-- The actual raw attaching boundary subcomplex with n+1 letters and count at most n. -/
def boundaryLayer (T : Data C) (x y : O) (n : ℕ) : (rawWordHom T x y).Subcomplex where
  obj q := {p | @Word.length O (scalarCategory C q) (fun x y => (T.target.Hom x y).obj q) x y p = n + 1 ∧
    countAt T q p ≤ n}
  map f p hp := ⟨(length_rawOperator T f p).trans hp.1, (countAt_rawOperator_le T f p).trans hp.2⟩

/-- Include the same original normalized word in the next actual simplicial length layer. -/
def layerInclusion (T : Data C) (x y : O) (n : ℕ) : (layer T x y n).toSSet ⟶ (layer T x y (n + 1)).toSSet :=
  Subfunctor.homOfLe (fun _ _ h => h.trans (Nat.le_succ n))

/-- Include the same original raw attaching boundary in the exact raw word stratum. -/
def boundaryInclusion (T : Data C) (x y : O) (n : ℕ) :
    (boundaryLayer T x y n).toSSet ⟶ (rawLayer T x y n).toSSet :=
  Subfunctor.homOfLe (fun _ _ h => h.1)

/-- Normalize the actual raw word stratum into the next original simplicial length layer. -/
def rawLayerNormalize (T : Data C) (x y : O) (n : ℕ) :
    (rawLayer T x y n).toSSet ⟶ (layer T x y (n + 1)).toSSet where
  app q := @RelativeGenerators.rawNormalize O (scalarCategory C q)
    (fun x y => (T.domain.Hom x y).obj q) (fun x y => (T.target.Hom x y).obj q)
    (fun {_ _} a => inclusionAt T q a) (fun {_ _} a => attachingAt T q a) x y n
  naturality q r f := by
    ext p
    apply Subtype.ext
    exact normalizeAt_operator T f p.val

/-- Normalize the actual raw attaching boundary into the previous original simplicial word layer. -/
def boundaryLayerNormalize (T : Data C) (x y : O) (n : ℕ) :
    (boundaryLayer T x y n).toSSet ⟶ (layer T x y n).toSSet where
  app q := @RelativeGenerators.boundaryNormalize O (scalarCategory C q)
    (fun x y => (T.domain.Hom x y).obj q) (fun x y => (T.target.Hom x y).obj q)
    (fun {_ _} a => inclusionAt T q a) (fun {_ _} a => attachingAt T q a) x y n
  naturality q r f := by
    ext p
    apply Subtype.ext
    exact normalizeAt_operator T f p.val

/-- The actual whole simplicial word-layer attaching square commutes on every original word. -/
theorem simplicialLayer_square (T : Data C) (x y : O) (n : ℕ) :
    boundaryLayerNormalize T x y n ≫ layerInclusion T x y n =
      boundaryInclusion T x y n ≫ rawLayerNormalize T x y n := by
  ext q p
  rfl

end CategoryTheory.SimplicialEnrichment.FixedObjects.RelativeAttachment
