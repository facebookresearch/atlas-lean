/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Homology.HomotopyCofiber

/-!
# Functorial homotopy cofibers

The homotopy cofiber as a functor on arrows of homological complexes, together
with the natural inclusion of each arrow's target.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
variable {ι : Type w} {c : ComplexShape ι} [DecidableRel c.Rel]

/-- The homotopy cofiber, functorial in strict commutative squares of complexes. -/
noncomputable def homotopyCofiberFunctor (h : ∀ j, ∃ i, c.Rel i j) :
    Arrow (HomologicalComplex C c) ⥤ HomologicalComplex C c where
  obj φ := homotopyCofiber φ.hom
  map {φ ψ} α := homotopyCofiber.mapArrowHom φ.hom ψ.hom h α
  map_id φ := homotopyCofiber.mapArrowHom_id φ.hom h
  map_comp {φ ψ χ} α β :=
    homotopyCofiber.mapArrowHom_comp φ.hom ψ.hom χ.hom h α β

@[simp]
lemma homotopyCofiberFunctor_obj (h : ∀ j, ∃ i, c.Rel i j)
    (φ : Arrow (HomologicalComplex C c)) :
    (homotopyCofiberFunctor h).obj φ = homotopyCofiber φ.hom :=
  rfl

@[simp]
lemma homotopyCofiberFunctor_map (h : ∀ j, ∃ i, c.Rel i j)
    {φ ψ : Arrow (HomologicalComplex C c)} (α : φ ⟶ ψ) :
    (homotopyCofiberFunctor h).map α =
      homotopyCofiber.mapArrowHom φ.hom ψ.hom h α :=
  rfl

/-- The target of an arrow includes naturally into its homotopy cofiber. -/
noncomputable def homotopyCofiberInr (h : ∀ j, ∃ i, c.Rel i j) :
    (Arrow.rightFunc : Arrow (HomologicalComplex C c) ⥤ _) ⟶
      homotopyCofiberFunctor h where
  app φ := homotopyCofiber.inr φ.hom
  naturality {φ ψ} α := by
    change α.right ≫ homotopyCofiber.inr ψ.hom =
      homotopyCofiber.inr φ.hom ≫
        homotopyCofiber.mapArrowHom φ.hom ψ.hom h α
    simp [homotopyCofiber.mapArrowHom]

@[simp]
lemma homotopyCofiberInr_app (h : ∀ j, ∃ i, c.Rel i j)
    (φ : Arrow (HomologicalComplex C c)) :
    (homotopyCofiberInr h).app φ = homotopyCofiber.inr φ.hom :=
  rfl

namespace homotopyCofiber

variable {F G F' G' : HomologicalComplex C c}
variable {phi : F ⟶ G} {psi : F' ⟶ G'}

@[reassoc]
lemma inr_mapArrowHom (h : ∀ j, ∃ i, c.Rel i j)
    (a : Arrow.mk phi ⟶ Arrow.mk psi) :
    inr phi ≫ mapArrowHom phi psi h a = a.right ≫ inr psi := by
  ext i
  simp [mapArrowHom]

@[reassoc]
lemma inrX_mapArrowHom (h : ∀ j, ∃ i, c.Rel i j)
    (a : Arrow.mk phi ⟶ Arrow.mk psi) (i : ι) :
    inrX phi i ≫ (mapArrowHom phi psi h a).f i =
      a.right.f i ≫ inrX psi i := by
  simpa only [inr_f, comp_f] using
    congrArg (fun k ↦ k.f i) (inr_mapArrowHom h a)

@[reassoc]
lemma inlX_mapArrowHom (h : ∀ j, ∃ i, c.Rel i j)
    (a : Arrow.mk phi ⟶ Arrow.mk psi) (i j : ι) (hji : c.Rel j i) :
    inlX phi i j hji ≫ (mapArrowHom phi psi h a).f j =
      a.left.f i ≫ inlX psi i j hji := by
  simp [mapArrowHom, desc_f _ _ _ _ _ hji,
    inrCompHomotopy_hom _ _ _ _ hji]

/-- Naturality of homotopy-cofiber universal morphism with compatibility only on related indices. -/
@[reassoc]
lemma mapArrowHom_desc_naturality_of_rel
    (hCofiber : ∀ j, ∃ i, c.Rel i j)
    (a : Arrow.mk phi ⟶ Arrow.mk psi)
    {K K' : HomologicalComplex C c}
    (alpha : G ⟶ K) (alpha' : G' ⟶ K')
    (h : _root_.Homotopy (phi ≫ alpha) 0)
    (h' : _root_.Homotopy (psi ≫ alpha') 0)
    (k : K ⟶ K')
    (halpha : a.right ≫ alpha' = alpha ≫ k)
    (hh : ∀ i j (_hji : c.Rel j i),
      a.left.f i ≫ h'.hom i j = h.hom i j ≫ k.f j) :
    mapArrowHom phi psi hCofiber a ≫ desc psi alpha' h' =
      desc phi alpha h ≫ k := by
  ext j
  by_cases hj : c.Rel j (c.next j)
  · apply ext_from_X phi (c.next j) j hj
    · simp only [HomologicalComplex.comp_f]
      rw [inlX_mapArrowHom_assoc, inlX_desc_f, inlX_desc_f_assoc]
      exact hh _ _ hj
    · simp only [HomologicalComplex.comp_f]
      rw [inrX_mapArrowHom_assoc, inrX_desc_f, inrX_desc_f_assoc]
      exact congrArg (fun z ↦ z.f j) halpha
  · apply ext_from_X' phi j hj
    simp only [HomologicalComplex.comp_f]
    rw [inrX_mapArrowHom_assoc, inrX_desc_f, inrX_desc_f_assoc]
    exact congrArg (fun z ↦ z.f j) halpha

/-- Naturality of the homotopy-cofiber universal morphism. -/
lemma mapArrowHom_desc_naturality
    (hCofiber : ∀ j, ∃ i, c.Rel i j)
    (a : Arrow.mk phi ⟶ Arrow.mk psi)
    {K K' : HomologicalComplex C c}
    (alpha : G ⟶ K) (alpha' : G' ⟶ K')
    (h : _root_.Homotopy (phi ≫ alpha) 0)
    (h' : _root_.Homotopy (psi ≫ alpha') 0)
    (k : K ⟶ K')
    (halpha : a.right ≫ alpha' = alpha ≫ k)
    (hh : ∀ i j, a.left.f i ≫ h'.hom i j = h.hom i j ≫ k.f j) :
    mapArrowHom phi psi hCofiber a ≫ desc psi alpha' h' =
      desc phi alpha h ≫ k :=
  mapArrowHom_desc_naturality_of_rel hCofiber a alpha alpha' h h' k halpha
    (fun i j _ => hh i j)

noncomputable def descShortComplex
    (S : ShortComplex (HomologicalComplex C c)) :
    homotopyCofiber S.f ⟶ S.X₃ :=
  desc S.f S.g (_root_.Homotopy.ofEq S.zero)

@[simp]
lemma descShortComplex_f
    (S : ShortComplex (HomologicalComplex C c)) (j : ι) :
    (descShortComplex S).f j = sndX S.f j ≫ S.g.f j := by
  unfold descShortComplex
  by_cases hj : c.Rel j (c.next j)
  · have h :=
        desc_f (φ := S.f) (α := S.g) (hα := _root_.Homotopy.ofEq S.zero) j
          (c.next j) hj
    simpa using h
  · exact desc_f' (φ := S.f) (α := S.g) (hα := _root_.Homotopy.ofEq S.zero) j hj

@[reassoc (attr := simp)]
lemma inr_descShortComplex
    (S : ShortComplex (HomologicalComplex C c)) :
    inr S.f ≫ descShortComplex S = S.g := by
  exact inr_desc S.f S.g (_root_.Homotopy.ofEq S.zero)

@[reassoc]
lemma descShortComplex_naturality
    (H : ∀ j, ∃ i, c.Rel i j)
    {S T : ShortComplex (HomologicalComplex C c)} (f : S ⟶ T) :
    mapArrowHom S.f T.f H
        ((ShortComplex.fFunctor :
            ShortComplex (HomologicalComplex C c) ⥤
              Arrow (HomologicalComplex C c)).map f) ≫
        descShortComplex T =
      descShortComplex S ≫ f.τ₃ := by
  apply mapArrowHom_desc_naturality_of_rel H
  · exact f.comm₂₃
  · intro i j _
    simp

/-- The universal homotopy-cofiber map to the third term of a short complex,
natural in the short complex. -/
noncomputable def descShortComplexNatTrans (H : ∀ j, ∃ i, c.Rel i j) :
    (ShortComplex.fFunctor :
        ShortComplex (HomologicalComplex C c) ⥤ Arrow (HomologicalComplex C c)) ⋙
        homotopyCofiberFunctor H ⟶
      (ShortComplex.π₃ :
        ShortComplex (HomologicalComplex C c) ⥤ HomologicalComplex C c) where
  app S := descShortComplex S
  naturality _ _ f := descShortComplex_naturality H f

/-- Component formula for `descShortComplexNatTrans`. -/
@[simp]
lemma descShortComplexNatTrans_app
    (H : ∀ j, ∃ i, c.Rel i j)
    (S : ShortComplex (HomologicalComplex C c)) :
    (descShortComplexNatTrans H).app S = descShortComplex S :=
  rfl

section

variable {A B K : ChainComplex C ℤ}

/-- Constructor for homotopies between morphisms from a chain-complex homotopy cofiber. -/
noncomputable def descHomotopy
    (φ : A ⟶ B) (f₁ f₂ : homotopyCofiber φ ⟶ K)
    (γ₁ : ∀ i j, A.X i ⟶ K.X j)
    (γ₁zero : ∀ i j, ¬(ComplexShape.down ℤ).Rel j i →
      γ₁ ((ComplexShape.down ℤ).next i) j = 0)
    (γ₂ : _root_.Homotopy (inr φ ≫ f₁) (inr φ ≫ f₂))
    (hsource : ∀ i j (hji : (ComplexShape.down ℤ).Rel j i),
      inlX φ i j hji ≫ f₁.f j =
        -A.d i ((ComplexShape.down ℤ).next i) ≫
              γ₁ ((ComplexShape.down ℤ).next i) j +
          φ.f i ≫ γ₂.hom i j +
          γ₁ i ((ComplexShape.down ℤ).prev j) ≫
              K.d ((ComplexShape.down ℤ).prev j) j +
          inlX φ i j hji ≫ f₂.f j) :
    _root_.Homotopy f₁ f₂ := by
  let γ : ∀ i j, (homotopyCofiber φ).X i ⟶ K.X j := fun i j =>
    fstX φ i ((ComplexShape.down ℤ).next i) (by simp) ≫
        γ₁ ((ComplexShape.down ℤ).next i) j +
      sndX φ i ≫ γ₂.hom i j
  refine
    { hom := γ
      zero := ?_
      comm := ?_ }
  · intro i j hij
    dsimp [γ]
    rw [γ₁zero i j hij, γ₂.zero i j hij, comp_zero, comp_zero, zero_add]
  · intro i
    have hi : (ComplexShape.down ℤ).Rel i ((ComplexShape.down ℤ).next i) := by simp
    apply ext_from_X φ ((ComplexShape.down ℤ).next i) i hi
    · rw [hsource _ _ hi]
      have hnext : (ComplexShape.down ℤ).Rel
          ((ComplexShape.down ℤ).next i)
          ((ComplexShape.down ℤ).next ((ComplexShape.down ℤ).next i)) := by simp
      have hprev : (ComplexShape.down ℤ).Rel
          ((ComplexShape.down ℤ).prev i) i := by simp
      rw [dNext_eq _ hi, prevD_eq _ hprev]
      simp only [homotopyCofiber_d, γ, Preadditive.comp_add, Category.assoc,
        inlX_d_assoc φ i ((ComplexShape.down ℤ).next i)
          ((ComplexShape.down ℤ).next ((ComplexShape.down ℤ).next i)) hi hnext,
        Preadditive.add_comp, Preadditive.neg_comp,
        inlX_fstX_assoc, inlX_sndX_assoc, inrX_fstX_assoc,
        inrX_sndX_assoc, zero_comp, comp_zero, neg_zero, zero_add, add_zero]
    · change (inr φ ≫ f₁).f i = _
      rw [γ₂.comm i]
      simp only [Preadditive.comp_add, comp_f]
      change _ =
        (inr φ).f i ≫ dNext i γ +
          (inr φ).f i ≫ prevD i γ +
            (inr φ).f i ≫ f₂.f i
      rw [← dNext_comp_left (inr φ) γ i, ← prevD_comp_left (inr φ) γ i]
      simp only [dNext, prevD, AddMonoidHom.mk'_apply, γ,
        Preadditive.comp_add, inr_f, inrX_fstX_assoc,
        zero_comp, zero_add, inrX_sndX_assoc]

end

end homotopyCofiber

end HomologicalComplex
