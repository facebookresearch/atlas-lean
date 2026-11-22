/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.RelativeWordSourceNormalization
import MathlibExt.AlgebraicTopology.SimplicialCategory.RelativeWordLayerAnodyne

/-!
# Full original finite word-layer source maps

The SAME enriched source comparison preserves exact normalized length;
the actual raw comparison preserves length and attaching-image count.
Both maps therefore restrict to the original finite layers and raw
attaching boundary. Their complete original normalization square is
retained, supplying the genuine layer pushout comparison.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.RelativeAttachment
open RelativeWords
variable {O : Type u} {C D : FixedObjects O}

/-- The unchanged actual enriched Hom source comparison preserves each original word-length layer. -/
def sourceLayerMap (T : Data C) (F : C ⟶ D) (a b : O) (n : ℕ) :
    (layer T a b n).toSSet ⟶ (layer (sourceChange T F) a b n).toSSet where
  app q := ↾fun p => ⟨(homMap (sourceChangeMap T F) a b).app q p.val, by
    have hl := normalizedSourceChange_length T F q p.val
    have hr := normalizedSourceChange_readback T F q p.val
    have he : wordLength (sourceChange T F) q ((homMap (sourceChangeMap T F) a b).app q p.val) =
        wordLength T q p.val :=
      (congrArg (wordLength (sourceChange T F) q) hr).symm.trans hl
    exact he.le.trans p.property⟩
  naturality q r f := by
    ext p
    apply Subtype.ext
    exact congrArg (fun h => h p.val) ((homMap (sourceChangeMap T F) a b).naturality f)

/-- The actual full raw source map restricted to its original exact finite-length stratum. -/
def sourceRawLayerMap (T : Data C) (F : C ⟶ D) (a b : O) (n : ℕ) :
    (rawLayer T a b n).toSSet ⟶ (rawLayer (sourceChange T F) a b n).toSSet where
  app q := ↾fun p => ⟨rawSourceChange T F q p.val,
    (rawSourceChange_length T F q p.val).trans p.property⟩
  naturality q r f := by
    ext p
    apply Subtype.ext
    exact rawSourceChange_operator T F f p.val

/-- The actual whole original raw word count is unchanged when the SAME inclusion and letters are retained. -/
theorem rawSourceChange_count (T : Data C) (F : C ⟶ D) (q : SimplexCategoryᵒᵖ)
    {a b : O} (p : RawWordAt T q a b) :
    countAt (sourceChange T F) q (rawSourceChange T F q p) = countAt T q p := by
  induction p with
  | old h => rfl
  | @cons a x y b h e p ih =>
    rw [rawSourceChange_cons]
    exact congrArg (fun n => RelativeGenerators.cost (C := O)
      (A := fun x y => (T.domain.Hom x y).obj q)
      (B := fun x y => (T.target.Hom x y).obj q)
      (fun {_ _} v => inclusionAt T q v) (a := x) (b := y) e + n) ih

/-- The SAME actual original raw source map restricts to its full original attaching boundary. -/
def sourceBoundaryLayerMap (T : Data C) (F : C ⟶ D) (a b : O) (n : ℕ) :
    (boundaryLayer T a b n).toSSet ⟶ (boundaryLayer (sourceChange T F) a b n).toSSet where
  app q := ↾fun p => ⟨rawSourceChange T F q p.val,
    (rawSourceChange_length T F q p.val).trans p.property.1,
    (rawSourceChange_count T F q p.val).le.trans p.property.2⟩
  naturality q r f := by
    ext p
    apply Subtype.ext
    exact rawSourceChange_operator T F f p.val

end CategoryTheory.SimplicialEnrichment.FixedObjects.RelativeAttachment
