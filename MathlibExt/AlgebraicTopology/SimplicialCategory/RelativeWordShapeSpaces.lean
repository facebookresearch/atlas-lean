/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.RelativeSimplicialWordLayers
import MathlibExt.CategoryTheory.Category.RelativeWordShapeEquivalence

/-!
# Actual simplicial factor spaces at the original finite word shapes

The factor objects are literal products of the supplied old Hom objects
and target-quiver objects. Their original simplex operators retain every
finite vertex label. The exact raw-word stratum is their actual simplicial
sum, with both inverse equations supplied by the original word equivalence.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.RelativeAttachment
open RelativeWords

variable {O : Type u} {C : FixedObjects O}

/-- The literal old-Hom and target-letter product for the actual finite supplied labels. -/
def shapeSpace (T : Data C) : {n : ℕ} → Shape O n → (a b : O) → SSet.{u}
  | 0, .nil, a, b => hom C a b
  | _n + 1, .cons x y s, a, b => hom C a x ⊗ (T.target.Hom x y ⊗ shapeSpace T s y b)

/-- Original factor simplices correspond to the canonical pure word factors, with explicit nullary lift. -/
def shapeCellsEquiv (T : Data C) (q : SimplexCategoryᵒᵖ) :
    {n : ℕ} → (s : Shape O n) → (a b : O) →
      (shapeSpace T s a b).obj q ≃
        @Cells O (scalarCategory C q) (fun x y => (T.target.Hom x y).obj q) n s a b
  | 0, .nil, _a, _b => Equiv.ulift.symm
  | _n + 1, .cons _x y s, _a, b =>
      Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr (Equiv.refl _) (shapeCellsEquiv T q s y b))

/-- Decode the same actual product factors to their entire original scalar raw word. -/
def shapeDecode (T : Data C) (q : SimplexCategoryᵒᵖ) {n : ℕ} (s : Shape O n)
    {a b : O} (p : (shapeSpace T s a b).obj q) : RawWordAt T q a b :=
  @decode O (scalarCategory C q) (fun x y => (T.target.Hom x y).obj q) n s a b
    (shapeCellsEquiv T q s a b p)

/-- The nullary actual shape retains its same original Hom simplex. -/
theorem shapeDecode_nil (T : Data C) (q : SimplexCategoryᵒᵖ) {a b : O} (f : (hom C a b).obj q) :
    shapeDecode T q Shape.nil f =
      @Word.old O (scalarCategory C q) (fun x y => (T.target.Hom x y).obj q) a b f := rfl

/-- Every original segment and target letter is decoded at the same supplied finite boundaries. -/
theorem shapeDecode_cons (T : Data C) (q : SimplexCategoryᵒᵖ) {n : ℕ} (s : Shape O n)
    {a x y b : O} (f : (hom C a x).obj q) (g : (T.target.Hom x y).obj q)
    (p : (shapeSpace T s y b).obj q) :
    shapeDecode T q (Shape.cons x y s) (f, g, p) =
      @Word.cons O (scalarCategory C q) (fun x y => (T.target.Hom x y).obj q) a x y b
        f g (shapeDecode T q s p) := rfl

/-- Every actual shape decodes with precisely its supplied finite original letter length. -/
theorem length_shapeDecode (T : Data C) (q : SimplexCategoryᵒᵖ) {n : ℕ} (s : Shape O n)
    {a b : O} (p : (shapeSpace T s a b).obj q) :
    @Word.length O (scalarCategory C q) (fun x y => (T.target.Hom x y).obj q) a b
      (shapeDecode T q s p) = n :=
  @length_decode O (scalarCategory C q) (fun x y => (T.target.Hom x y).obj q) n s a b
    (shapeCellsEquiv T q s a b p)

/-- The actual original factor operators decode to the same whole original raw-word operators. -/
theorem rawOperator_shapeDecode (T : Data C) {q r : SimplexCategoryᵒᵖ} (f : q ⟶ r)
    {n : ℕ} (s : Shape O n) {a b : O} (p : (shapeSpace T s a b).obj q) :
    rawOperator T f (shapeDecode T q s p) = shapeDecode T r s ((shapeSpace T s a b).map f p) := by
  induction s generalizing a b with
  | nil => rfl
  | cons x y s ih =>
      rcases p with ⟨h, g, p⟩
      rw [shapeDecode_cons, rawOperator_cons]
      change _ = @Word.cons O (scalarCategory C r) (fun x y => (T.target.Hom x y).obj r)
        a x y b ((hom C a x).map f h) ((T.target.Hom x y).map f g)
        (shapeDecode T r s ((shapeSpace T s y b).map f p))
      rw [ih]

/-- The actual simplicial sum of all original finite label shapes of the supplied length. -/
def shapeSum (T : Data C) (a b : O) (n : ℕ) : SSet.{u} where
  obj q := Σ s : Shape O n, (shapeSpace T s a b).obj q
  map f := ↾fun p => ⟨p.1, (shapeSpace T p.1 a b).map f p.2⟩
  map_id q := by
    apply ConcreteCategory.hom_ext
    intro p
    rcases p with ⟨s, p⟩
    exact congrArg (Sigma.mk (β := fun s : Shape O n => (shapeSpace T s a b).obj q) s)
      (congrArg (fun f => f p) ((shapeSpace T s a b).map_id q))
  map_comp {q r t} f g := by
    apply ConcreteCategory.hom_ext
    intro p
    rcases p with ⟨s, p⟩
    exact congrArg (Sigma.mk (β := fun s : Shape O n => (shapeSpace T s a b).obj t) s)
      (congrArg (fun f => f p) ((shapeSpace T s a b).map_comp f g))

/-- The exact degreewise raw-word equivalence decodes the literal original simplicial factors. -/
def shapeSumEquiv (T : Data C) (a b : O) (n : ℕ) (q : SimplexCategoryᵒᵖ) :
    (shapeSum T a b (n + 1)).obj q ≃ ((rawLayer T a b n).toSSet.obj q) :=
  (Equiv.sigmaCongrRight (fun s => shapeCellsEquiv T q s a b)).trans
    (@fixedLengthFactorsEquiv O (scalarCategory C q) (fun x y => (T.target.Hom x y).obj q)
      (n + 1) a b)

/-- The exact raw-word equivalence reads the entire supplied product, without changing any vertex. -/
theorem shapeSumEquiv_apply (T : Data C) (a b : O) (n : ℕ) (q : SimplexCategoryᵒᵖ)
    (p : (shapeSum T a b (n + 1)).obj q) :
    (shapeSumEquiv T a b n q p).val = shapeDecode T q p.1 p.2 := rfl

/-- The whole simplicial factor sum is isomorphic to the actual exact raw-word stratum. -/
def shapeSumIso (T : Data C) (a b : O) (n : ℕ) : shapeSum T a b (n + 1) ≅ (rawLayer T a b n).toSSet :=
  NatIso.ofComponents (fun q => (shapeSumEquiv T a b n q).toIso) (by
    intro q r f
    ext p
    apply Subtype.ext
    exact (rawOperator_shapeDecode T f p.1 p.2).symm)

end CategoryTheory.SimplicialEnrichment.FixedObjects.RelativeAttachment
