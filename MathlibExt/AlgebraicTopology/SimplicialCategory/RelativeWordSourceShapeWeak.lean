/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.RelativeWordSourceShapeMaps
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectModelClasses
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FullProductWeakEquivalences

/-!
# Actual original shape factors are weak under original weak source change

The original finite shapes have their literal old-Hom and unchanged
new-letter factors. Canonical original simplicial-set product weakness
proves weakness of each SAME complete shape map. Its decoding equation
retains the actual full raw source word map and every original operator.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.RelativeAttachment
open RelativeWords
variable {O : Type u} {C D : FixedObjects O}

/-- The SAME full original shape map decodes to the unchanged actual raw source-comparison word. -/
theorem shapeSourceChange_decode (T : Data C) (F : C ⟶ D) (q : SimplexCategoryᵒᵖ)
    {n : ℕ} (s : Shape O n) {a b : O} (p : (shapeSpace T s a b).obj q) :
    shapeDecode (sourceChange T F) q s ((shapeSourceChange T F s a b).app q p) =
      rawSourceChange T F q (shapeDecode T q s p) := by
  induction s generalizing a b with
  | nil => rfl
  | cons x y s ih =>
    rcases p with ⟨h, e, p⟩
    rw [shapeDecode_cons, rawSourceChange_cons]
    change @Word.cons O (scalarCategory D q) _ a x y b ((homMap F a x).app q h) e
        (shapeDecode (sourceChange T F) q s ((shapeSourceChange T F s y b).app q p)) = _
    exact congrArg (fun p => @Word.cons O (scalarCategory D q) _ a x y b
      ((homMap F a x).app q h) e p) (ih p)

/-- Every SAME original finite shape map is weak from the actual complete original Hom weaknesses, with no Kan source
premise. -/
theorem shapeSourceChange_weak (T : Data C) (F : C ⟶ D)
    (hF : FixedObjectModel.weakEquivalences O F) {n : ℕ} (s : Shape O n) (a b : O) :
    SSet.realizationWeakEquivalences (shapeSourceChange T F s a b) := by
  have h := (FixedObjectModel.weakEquivalences_iff F).mp hF
  induction s generalizing a b with
  | nil => exact h a b
  | cons x y s ih =>
    exact SSet.realizationWeakEquivalences.tensorHom (homMap F a x)
      (𝟙 (T.target.Hom x y) ⊗ₘ shapeSourceChange T F s y b) (h a x)
        (SSet.realizationWeakEquivalences.tensorHom (𝟙 _) _
          (SSet.realizationWeakEquivalences.id_mem _) (ih y b))

end CategoryTheory.SimplicialEnrichment.FixedObjects.RelativeAttachment
