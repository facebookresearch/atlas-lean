/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.HomotopyCofiberHomotopyMap

/-!
# Coherence of native cofiber maps for homotopy squares

Native homotopy composition pastes two actual squares. The resulting cofiber
map equals the composite of the original maps, with the identity square giving
the identity map. Related-degree homotopy components suffice to determine the
cofiber map. All complex shapes and all native cofiber coordinates are retained.

-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive

universe u v w

namespace HomologicalComplex.homotopyCofiber

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]
  {ι : Type w} {c : ComplexShape ι} [DecidableRel c.Rel]
  {F₁ G₁ F₂ G₂ F₃ G₃ : HomologicalComplex C c}
  (φ₁ : F₁ ⟶ G₁) (φ₂ : F₂ ⟶ G₂) (φ₃ : F₃ ⟶ G₃)
  (hc : ∀ j : ι, ∃ i, c.Rel i j)
  (a₁ : F₁ ⟶ F₂) (b₁ : G₁ ⟶ G₂) (a₂ : F₂ ⟶ F₃) (b₂ : G₂ ⟶ G₃)
  (H₁ : _root_.Homotopy (φ₁ ≫ b₁) (a₁ ≫ φ₂))
  (H₂ : _root_.Homotopy (φ₂ ≫ b₂) (a₂ ≫ φ₃))

/-- Paste the actual homotopies using native composition and associativity. -/
def composeMapHomotopy :
    _root_.Homotopy (φ₁ ≫ (b₁ ≫ b₂)) ((a₁ ≫ a₂) ≫ φ₃) :=
  (_root_.Homotopy.ofEq (Category.assoc φ₁ b₁ b₂).symm).trans
    ((H₁.compRight b₂).trans
      ((_root_.Homotopy.ofEq (Category.assoc a₁ φ₂ b₂)).trans
        ((H₂.compLeft a₁).trans
          (_root_.Homotopy.ofEq (Category.assoc a₁ a₂ φ₃).symm))))

omit [HasZeroObject C] [HasBinaryBiproducts C] [DecidableRel c.Rel] in
/-- The off-diagonal component of the pasted square is the native sum. -/
theorem composeMapHomotopy_hom (i j : ι) :
    (composeMapHomotopy φ₁ φ₂ φ₃ a₁ b₁ a₂ b₂ H₁ H₂).hom i j =
      H₁.hom i j ≫ b₂.f j + a₁.f i ≫ H₂.hom i j := by
  simp only [composeMapHomotopy, _root_.Homotopy.trans_hom,
    _root_.Homotopy.ofEq_hom, _root_.Homotopy.compRight_hom,
    _root_.Homotopy.compLeft_hom, Pi.zero_apply,
    zero_add, add_zero]

/-- Native cofiber maps compose using the actual pasted homotopy square. -/
theorem mapOfHomotopy_comp :
    mapOfHomotopy φ₁ φ₃ hc (a₁ ≫ a₂) (b₁ ≫ b₂)
        (composeMapHomotopy φ₁ φ₂ φ₃ a₁ b₁ a₂ b₂ H₁ H₂) =
      mapOfHomotopy φ₁ φ₂ hc a₁ b₁ H₁ ≫ mapOfHomotopy φ₂ φ₃ hc a₂ b₂ H₂ := by
  ext j
  by_cases hj : c.Rel j (c.next j)
  · apply ext_from_X φ₁ (c.next j) j hj
    · simp only [HomologicalComplex.comp_f, inlX_mapOfHomotopy,
        inlX_mapOfHomotopy_assoc, composeMapHomotopy_hom,
        add_comp, comp_add, Category.assoc, inrX_mapOfHomotopy_assoc,
        inlX_mapOfHomotopy_assoc, add_assoc]
      rw [inrX_mapOfHomotopy]
    · simp only [HomologicalComplex.comp_f, inrX_mapOfHomotopy,
        inrX_mapOfHomotopy_assoc, Category.assoc]
  · apply ext_from_X' φ₁ j hj
    simp only [HomologicalComplex.comp_f, inrX_mapOfHomotopy,
      inrX_mapOfHomotopy_assoc, Category.assoc]

section Identity

variable {F G : HomologicalComplex C c} (φ : F ⟶ G)

omit [HasZeroObject C] in
/-- The actual identity square gives the native identity cofiber map. -/
@[simp]
theorem mapOfHomotopy_id :
    mapOfHomotopy φ φ hc (𝟙 F) (𝟙 G) (_root_.Homotopy.ofEq (by simp)) = 𝟙 _ := by
  rw [mapOfHomotopy_ofEq]
  have h : Arrow.homMk' (𝟙 F) (𝟙 G) (by simp) = 𝟙 (Arrow.mk φ) := rfl
  rw [h, mapArrowHom_id]

end Identity

section Extensionality

variable {F G F' G' : HomologicalComplex C c}
  (φ : F ⟶ G) (ψ : F' ⟶ G') (a : F ⟶ F') (b : G ⟶ G')
  (H H' : _root_.Homotopy (φ ≫ b) (a ≫ ψ))

omit [HasZeroObject C] in
/-- Only the related-degree components of the supplied homotopy affect the actual cofiber map. -/
theorem mapOfHomotopy_congr
    (h : ∀ i j (_ : c.Rel j i), H.hom i j = H'.hom i j) :
    mapOfHomotopy φ ψ hc a b H = mapOfHomotopy φ ψ hc a b H' := by
  ext j
  by_cases hj : c.Rel j (c.next j)
  · apply ext_from_X φ (c.next j) j hj
    · rw [inlX_mapOfHomotopy, inlX_mapOfHomotopy, h _ _ hj]
    · rw [inrX_mapOfHomotopy, inrX_mapOfHomotopy]
  · apply ext_from_X' φ j hj
    rw [inrX_mapOfHomotopy, inrX_mapOfHomotopy]

end Extensionality

end HomologicalComplex.homotopyCofiber

end
