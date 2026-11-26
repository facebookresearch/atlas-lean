/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.RelativeWordSourceChange
import MathlibExt.AlgebraicTopology.SimplicialCategory.RelativeWordShapeSpaces

/-!
# The original source comparison retains raw words and exact original shapes

Every old segment is mapped by the unchanged original Hom map and each
original target letter is retained. The literal source-change quivers
make the actual raw word map preserve exact finite length and all scalar
operators. Every full original shape factor map is retained explicitly.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.RelativeAttachment
open RelativeWords
variable {O : Type u} {C D : FixedObjects O}

/-- Relabel every actual original raw Hom segment while retaining each unchanged original target letter. -/
def rawSourceChange (T : Data C) (F : C ⟶ D) (q : SimplexCategoryᵒᵖ)
    {x y : O} (p : RawWordAt T q x y) : RawWordAt (sourceChange T F) q x y :=
  @relabel O (scalarCategory C q) (fun x y => (T.target.Hom x y).obj q)
    O (scalarCategory D q) (fun x y => (T.target.Hom x y).obj q)
    (scalarFunctor F q) (fun {_ _} e => e) x y p

/-- The raw source map keeps every actual old segment and complete unchanged target-letter tail. -/
theorem rawSourceChange_cons (T : Data C) (F : C ⟶ D) (q : SimplexCategoryᵒᵖ)
    {a x y b : O} (h : (hom C a x).obj q) (e : (T.target.Hom x y).obj q)
    (p : RawWordAt T q y b) :
    rawSourceChange T F q (@Word.cons O (scalarCategory C q) _ a x y b h e p) =
      @Word.cons O (scalarCategory D q) _ a x y b ((homMap F a x).app q h) e
        (rawSourceChange T F q p) :=
  @relabel_cons O (scalarCategory C q) (fun x y => (T.target.Hom x y).obj q)
    O (scalarCategory D q) (fun x y => (T.target.Hom x y).obj q)
    (scalarFunctor F q) (fun {_ _} e => e) a x y b h e p

/-- The SAME full raw word map retains the exact original finite target-letter count. -/
theorem rawSourceChange_length (T : Data C) (F : C ⟶ D) (q : SimplexCategoryᵒᵖ)
    {x y : O} (p : RawWordAt T q x y) :
    @Word.length O (scalarCategory D q) (fun x y => (T.target.Hom x y).obj q) x y
      (rawSourceChange T F q p) =
        @Word.length O (scalarCategory C q) (fun x y => (T.target.Hom x y).obj q) x y p :=
  @length_relabel O (scalarCategory C q) (fun x y => (T.target.Hom x y).obj q)
    O (scalarCategory D q) (fun x y => (T.target.Hom x y).obj q)
    (scalarFunctor F q) (fun {_ _} e => e) x y p

/-- The actual source change commutes with every SAME full original raw simplex operator. -/
theorem rawSourceChange_operator (T : Data C) (F : C ⟶ D) {q r : SimplexCategoryᵒᵖ} (f : q ⟶ r)
    {x y : O} (p : RawWordAt T q x y) :
    rawSourceChange T F r (rawOperator T f p) =
      rawOperator (sourceChange T F) f (rawSourceChange T F q p) := by
  induction p with
  | @old x y h =>
    change @Word.old O (scalarCategory D r) _ x y
        ((homMap F x y).app r ((hom C x y).map f h)) =
      @Word.old O (scalarCategory D r) _ x y
        ((hom D x y).map f ((homMap F x y).app q h))
    exact congrArg (fun h => @Word.old O (scalarCategory D r) _ x y h)
      (scalarFunctor_operator F f x y h)
  | @cons a x y b h e p ih =>
    rw [rawOperator_cons, rawSourceChange_cons, rawSourceChange_cons]
    have ht := @rawOperator_cons O D (sourceChange T F) q r f a x y b
      ((homMap F a x).app q h) e (rawSourceChange T F q p)
    have hh := scalarFunctor_operator F f a x h
    exact (congrArg₂ (fun h p => @Word.cons O (scalarCategory D r) _ a x y b h
      ((T.target.Hom x y).map f e) p) hh ih).trans ht.symm

/-- The SAME entire source-change map on raw words is a genuine original simplicial map. -/
def rawSourceChangeHom (T : Data C) (F : C ⟶ D) (x y : O) :
    rawWordHom T x y ⟶ rawWordHom (sourceChange T F) x y where
  app q := ↾fun p => rawSourceChange T F q p
  naturality q r f := by ext p; exact rawSourceChange_operator T F f p

/-- Every actual original finite shape factor retains the SAME target letters and original full Hom maps. -/
def shapeSourceChange (T : Data C) (F : C ⟶ D) :
    {n : ℕ} → (s : Shape O n) → (a b : O) → shapeSpace T s a b ⟶ shapeSpace (sourceChange T F) s a b
  | 0, .nil, a, b => homMap F a b
  | _n + 1, .cons x y s, a, b => homMap F a x ⊗ₘ (𝟙 (T.target.Hom x y) ⊗ₘ shapeSourceChange T F s y b)

end CategoryTheory.SimplicialEnrichment.FixedObjects.RelativeAttachment
