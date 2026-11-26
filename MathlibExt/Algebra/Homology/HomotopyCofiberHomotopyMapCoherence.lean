/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.HomotopyCofiberHomotopyMap

/-!
# Composition and extensionality of homotopy-square cofiber maps

In a preadditive category, two composable homotopy squares with homotopies
H₁:b₁∘φ₁ ∼ φ₂∘a₁ and H₂:b₂∘φ₂ ∼ φ₃∘a₂ paste to a homotopy
from (b₂∘b₁)∘φ₁ to φ₃∘(a₂∘a₁). Its component is
H_paste(i,j)=b₂,j ∘ H₁(i,j)+H₂(i,j) ∘ a₁,i.

For cofibers in a preadditive category with a zero object and binary
biproducts, a decidable shape relation and predecessors in every degree,
the map of the pasted square equals the composite of the two cofiber maps.
The identity square gives the identity cofiber map. For fixed vertical
maps, equality of the homotopy components H(i,j) on c.Rel(j,i) determines
the cofiber map.
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

/-- Let C be preadditive and let φ₁:F₁ → G₁, φ₂:F₂ → G₂ and φ₃:F₃ → G₃
be maps of complexes of one shape. For a₁:F₁ → F₂, b₁:G₁ → G₂,
a₂:F₂ → F₃, b₂:G₂ → G₃ and homotopies
H₁:b₁∘φ₁ ∼ φ₂∘a₁, H₂:b₂∘φ₂ ∼ φ₃∘a₂,
the pasted homotopy (b₂∘b₁)∘φ₁ ∼ φ₃∘(a₂∘a₁). -/
def composeMapHomotopy :
    _root_.Homotopy (φ₁ ≫ (b₁ ≫ b₂)) ((a₁ ≫ a₂) ≫ φ₃) :=
  (_root_.Homotopy.ofEq (Category.assoc φ₁ b₁ b₂).symm).trans
    ((H₁.compRight b₂).trans
      ((_root_.Homotopy.ofEq (Category.assoc a₁ φ₂ b₂)).trans
        ((H₂.compLeft a₁).trans
          (_root_.Homotopy.ofEq (Category.assoc a₁ a₂ φ₃).symm))))

omit [HasZeroObject C] [HasBinaryBiproducts C] [DecidableRel c.Rel] in
/-- In a preadditive category, for two homotopy squares
H₁:b₁∘φ₁ ∼ φ₂∘a₁ and H₂:b₂∘φ₂ ∼ φ₃∘a₂ of complexes of one
shape, the pasted homotopy has component, for all indices i,j,
H_paste(i,j)=b₂,j ∘ H₁(i,j)+H₂(i,j) ∘ a₁,i. -/
theorem composeMapHomotopy_hom (i j : ι) :
    (composeMapHomotopy φ₁ φ₂ φ₃ a₁ b₁ a₂ b₂ H₁ H₂).hom i j =
      H₁.hom i j ≫ b₂.f j + a₁.f i ≫ H₂.hom i j := by
  simp only [composeMapHomotopy, _root_.Homotopy.trans_hom,
    _root_.Homotopy.ofEq_hom, _root_.Homotopy.compRight_hom,
    _root_.Homotopy.compLeft_hom, Pi.zero_apply,
    zero_add, add_zero]

/-- Let C be preadditive with a zero object and binary biproducts,
and let c have decidable differential relation and a predecessor in
every degree. For composable homotopy squares (a₁,b₁,H₁) and
(a₂,b₂,H₂) from φ₁ to φ₂ to φ₃, the cofiber map of the pasted
square equals M(a₂,b₂,H₂) ∘ M(a₁,b₁,H₁), with vertical maps
a₂∘a₁ and b₂∘b₁ and pasted homotopy
H_paste(i,j)=b₂,j∘H₁(i,j)+H₂(i,j)∘a₁,i. -/
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
/-- In a preadditive category C with binary biproducts, for a complex shape
c with decidable differential relation and a predecessor in every degree,
the cofiber map of the identity square on φ:F → G, with vertical
maps 1_F,1_G and the equality's zero-component homotopy, is the
identity of Cofib(φ). -/
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
/-- Let C be preadditive with binary biproducts, c have decidable
differential relation and a predecessor in every degree, and
φ:F → G, ψ:F′ → G′, a:F → F′, b:G → G′ be fixed.
If homotopies H,H′:b∘φ ∼ ψ∘a have equal components
H(i,j)=H′(i,j) whenever c.Rel(j,i), they induce equal maps
Cofib(φ) → Cofib(ψ). -/
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
