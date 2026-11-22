/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FullProductWeakEquivalences
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.AllCofibrant
import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantCube

/-!
# Weakness of the SAME full original union-product map

The native original union-product square has its genuine full pushout
universal property. The actual two ambient maps and their subcomplex
restrictions retain every original simplex. Weakness of the original
pieces gives weakness of the SAME full union map by the actual cube lemma.
No desired attaching-boundary weakness is supplied as an input.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra MonoidalCategory
open scoped SSet.modelCategoryQuillen

namespace SSet.Subcomplex

/-- Restrict the SAME actual original tensor map to its full original union-product subcomplex. -/
def unionProdMap {X X' Y Y' : SSet.{u}} (A : X.Subcomplex) (B : Y.Subcomplex)
    (A' : X'.Subcomplex) (B' : Y'.Subcomplex) (f : X ⟶ X') (g : Y ⟶ Y')
    (hf : ∀ q x, x ∈ A.obj q → f.app q x ∈ A'.obj q)
    (hg : ∀ q y, y ∈ B.obj q → g.app q y ∈ B'.obj q) :
    (A.unionProd B).toSSet ⟶ (A'.unionProd B').toSSet where
  app q := ↾fun p => ⟨(f.app q p.val.1, g.app q p.val.2), by
    apply (mem_unionProd_iff A' B' _).mpr
    rcases (mem_unionProd_iff A B p.val).mp p.property with h | h
    · exact Or.inl (hg q p.val.2 h)
    · exact Or.inr (hf q p.val.1 h)⟩
  naturality q r a := by
    ext p
    apply Subtype.ext
    exact Prod.ext (congrArg (fun k => k p.val.1) (f.naturality a))
      (congrArg (fun k => k p.val.2) (g.naturality a))

/-- The SAME actual original union-product map retains its whole ambient tensor map. -/
theorem unionProdMap_ι {X X' Y Y' : SSet.{u}} (A : X.Subcomplex) (B : Y.Subcomplex)
    (A' : X'.Subcomplex) (B' : Y'.Subcomplex) (f : X ⟶ X') (g : Y ⟶ Y')
    (hf : ∀ q x, x ∈ A.obj q → f.app q x ∈ A'.obj q)
    (hg : ∀ q y, y ∈ B.obj q → g.app q y ∈ B'.obj q) :
    unionProdMap A B A' B' f g hf hg ≫ (A'.unionProd B').ι = (A.unionProd B).ι ≫ (f ⊗ₘ g) := rfl

/-- Three genuine original product pieces give weakness of the unchanged full union-product map. -/
theorem unionProdMap_weak {X X' Y Y' : SSet.{u}} (A : X.Subcomplex) (B : Y.Subcomplex)
    (A' : X'.Subcomplex) (B' : Y'.Subcomplex) (f : X ⟶ X') (g : Y ⟶ Y')
    (hf : ∀ q x, x ∈ A.obj q → f.app q x ∈ A'.obj q)
    (hg : ∀ q y, y ∈ B.obj q → g.app q y ∈ B'.obj q)
    (a : A.toSSet ⟶ A'.toSSet) (b : B.toSSet ⟶ B'.toSSet)
    (ha : a ≫ A'.ι = A.ι ≫ f) (hb : b ≫ B'.ι = B.ι ≫ g)
    (wf : realizationWeakEquivalences f) (wg : realizationWeakEquivalences g)
    (wa : realizationWeakEquivalences a) (wb : realizationWeakEquivalences b) :
    realizationWeakEquivalences (unionProdMap A B A' B' f g hf hg) := by
  let m := unionProdMap A B A' B' f g hf hg
  have h1 : unionProd.ι₁ A B ≫ m = (f ⊗ₘ b) ≫ unionProd.ι₁ A' B' := by
    ext q p
    apply Subtype.ext
    exact Prod.ext rfl (congrArg (fun k => k.app q p.2) hb).symm
  have h2 : unionProd.ι₂ A B ≫ m = (a ⊗ₘ g) ≫ unionProd.ι₂ A' B' := by
    ext q p
    apply Subtype.ext
    exact Prod.ext (congrArg (fun k => k.app q p.1) ha).symm rfl
  have hi : (A.ι ▷ B.toSSet) ≫ (f ⊗ₘ b) = (a ⊗ₘ b) ≫ (A'.ι ▷ B'.toSSet) := by
    apply NatTrans.ext
    funext q
    apply ConcreteCategory.hom_ext
    intro p
    change (f.app q p.1.val, b.app q p.2) = ((a.app q p.1).val, b.app q p.2)
    exact Prod.ext (congrArg (fun k => k.app q p.1) ha).symm rfl
  have hj : (A.toSSet ◁ B.ι) ≫ (a ⊗ₘ g) = (a ⊗ₘ b) ≫ (A'.toSSet ◁ B'.ι) := by
    apply NatTrans.ext
    funext q
    apply ConcreteCategory.hom_ext
    intro p
    change (a.app q p.1, g.app q p.2.val) = (a.app q p.1, (b.app q p.2).val)
    exact Prod.ext rfl (congrArg (fun k => k.app q p.2) hb).symm
  let _ : WeakEquivalence (a ⊗ₘ b) :=
    (weakEquivalence_iff _).mpr (realizationWeakEquivalences.tensorHom a b wa wb)
  let _ : WeakEquivalence (f ⊗ₘ b) :=
    (weakEquivalence_iff _).mpr (realizationWeakEquivalences.tensorHom f b wf wb)
  let _ : WeakEquivalence (a ⊗ₘ g) :=
    (weakEquivalence_iff _).mpr (realizationWeakEquivalences.tensorHom a g wa wg)
  let _ : Mono (A.ι ▷ B.toSSet) := by
    change Mono ((tensorRight B.toSSet).map A.ι)
    infer_instance
  let _ : Mono (A'.ι ▷ B'.toSSet) := by
    change Mono ((tensorRight B'.toSSet).map A'.ι)
    infer_instance
  let _ : Cofibration (A.ι ▷ B.toSSet) := (cofibration_iff _).mpr
    (inferInstance : Mono (A.ι ▷ B.toSSet))
  let _ : Cofibration (A'.ι ▷ B'.toSSet) := (cofibration_iff _).mpr
    (inferInstance : Mono (A'.ι ▷ B'.toSSet))
  exact (weakEquivalence_iff _).mp (weakEquivalence_map_of_isPushouts_of_cofibrant
    (unionProd.isPushout A B) (unionProd.isPushout A' B')
    hi hj h1 h2)

end SSet.Subcomplex
