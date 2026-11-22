/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.RelativeWordSourceShapeWeak
import MathlibExt.AlgebraicTopology.SimplicialCategory.RelativeWordShapeBoundaries
import MathlibExt.AlgebraicTopology.SimplicialSet.OriginalUnionProductWeakMap

/-!
# The actual original attaching shape boundaries retain source maps

Source change keeps the SAME target-quiver inclusion, so original
attaching-image boundary membership is retained in both directions.
The whole shape source map restricts to its genuine full original
boundary, with every original scalar operator and label retained.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.RelativeAttachment
open RelativeWords
variable {O : Type u} {C D : FixedObjects O}

/-- The SAME original finite attaching-image condition is preserved and reflected by actual source change. -/
theorem shapeSourceChange_boundary_iff (T : Data C) (F : C ⟶ D) (q : SimplexCategoryᵒᵖ)
    {n : ℕ} (s : Shape O n) {a b : O} (p : (shapeSpace T s a b).obj q) :
    (shapeSourceChange T F s a b).app q p ∈ (shapeBoundary (sourceChange T F) s a b).obj q ↔
      p ∈ (shapeBoundary T s a b).obj q := by
  induction s generalizing a b with
  | nil => exact Iff.rfl
  | cons x y s ih =>
    rcases p with ⟨h, e, p⟩
    have outer {X Y : SSet.{u}} (B : Y.Subcomplex) (x : X.obj q) (y : Y.obj q) :
        (x, y) ∈ ((⊥ : X.Subcomplex).unionProd B).obj q ↔ y ∈ B.obj q := by
      constructor
      · intro h
        rcases (SSet.Subcomplex.mem_unionProd_iff (⊥ : X.Subcomplex) B (x, y)).mp h with h | h
        · exact h
        · exact h.elim
      · intro h
        exact (SSet.Subcomplex.mem_unionProd_iff (⊥ : X.Subcomplex) B (x, y)).mpr (Or.inl h)
    have h0 : (shapeSourceChange T F (Shape.cons x y s) a b).app q (h, e, p) =
        ((homMap F a x).app q h, e, (shapeSourceChange T F s y b).app q p) := rfl
    exact (congrArg (fun v => v ∈ (shapeBoundary (sourceChange T F) (Shape.cons x y s) a b).obj q) h0).to_iff.trans
      ((outer ((SSet.Subcomplex.range (T.inclusion x y)).unionProd
        (shapeBoundary (sourceChange T F) s y b)) _ _).trans
        ((SSet.Subcomplex.mem_unionProd_iff (SSet.Subcomplex.range (T.inclusion x y))
          (shapeBoundary (sourceChange T F) s y b) (e, (shapeSourceChange T F s y b).app q p)).trans
          ((or_congr (ih p) Iff.rfl).trans
            ((SSet.Subcomplex.mem_unionProd_iff (SSet.Subcomplex.range (T.inclusion x y))
              (shapeBoundary T s y b) (e, p)).symm.trans
                (outer ((SSet.Subcomplex.range (T.inclusion x y)).unionProd (shapeBoundary T s y b)) h (e, p)).symm))))


/-- The actual full original shape source map restricted to its SAME attaching boundary. -/
def shapeBoundarySourceChange (T : Data C) (F : C ⟶ D) {n : ℕ}
    (s : Shape O n) (a b : O) :
    (shapeBoundary T s a b).toSSet ⟶ (shapeBoundary (sourceChange T F) s a b).toSSet where
  app q := ↾fun p => ⟨(shapeSourceChange T F s a b).app q p.val,
    (shapeSourceChange_boundary_iff T F q s p.val).mpr p.property⟩
  naturality q r f := by
    ext p
    apply Subtype.ext
    exact congrArg (fun g => g p.val) ((shapeSourceChange T F s a b).naturality f)

/-- Every SAME original full boundary source map retains the complete ambient original shape square. -/
theorem shapeBoundarySourceChange_ι (T : Data C) (F : C ⟶ D) {n : ℕ}
    (s : Shape O n) (a b : O) :
    shapeBoundarySourceChange T F s a b ≫ (shapeBoundary (sourceChange T F) s a b).ι =
      (shapeBoundary T s a b).ι ≫ shapeSourceChange T F s a b := rfl

end CategoryTheory.SimplicialEnrichment.FixedObjects.RelativeAttachment
