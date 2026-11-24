/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.Embedding.Restriction
public import MathlibExt.Algebra.Homology.HomotopyCofiber
public import MathlibExt.Algebra.Homology.HomotopyCofiberProjection

/-!
# Restriction preserves homotopy cofibers

Homotopy-cofiber existence is preserved by restriction along an embedding
of complex shapes. The required binary biproducts are transported along
`e.rel`. If the image is closed under outgoing edges, restriction commutes
naturally with homotopy cofibers, including their maps from short complexes.
-/

@[expose] public section
universe u v

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace HomologicalComplex.HasHomotopyCofiber

/-- Transports homotopy-cofiber existence along restriction by a complex-shape embedding. -/
theorem restrictionMap
    {C : Type u} [Category.{v} C] [Preadditive C]
    {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
    {F G : HomologicalComplex C c'} (φ : F ⟶ G)
    (e : c.Embedding c') [e.IsRelIff] [HomologicalComplex.HasHomotopyCofiber φ] :
    HomologicalComplex.HasHomotopyCofiber
      (HomologicalComplex.restrictionMap φ e) where
  hasBinaryBiproduct i j hij :=
    HomologicalComplex.HasHomotopyCofiber.hasBinaryBiproduct (φ := φ) (e.f i) (e.f j)
      (e.rel hij)

end HomologicalComplex.HasHomotopyCofiber

namespace HomologicalComplex

/-- Restriction at the same image degree has the identity component isomorphism. -/
@[simp]
lemma restrictionXIso_rfl
    {C : Type u} [Category.{v} C] [Preadditive C]
    {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
    (K : HomologicalComplex C c') (e : c.Embedding c') [e.IsRelIff] (i : ι) :
    K.restrictionXIso e (rfl : e.f i = e.f i) = Iso.refl _ :=
  rfl

end HomologicalComplex

namespace HomologicalComplex.homotopyCofiber

open CategoryTheory.Limits

universe w

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
variable {ι : Type w} {ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

section Object

variable {F G : HomologicalComplex C c'} (φ : F ⟶ G)
variable (e : c.Embedding c') [e.IsTruncGE]

/-- Outgoing closure reflects the absence of a successor edge at an image degree. -/
lemma not_rel_next_of_not_rel_next (i : ι)
    (hi : ¬ c.Rel i (c.next i)) :
    ¬ c'.Rel (e.f i) (c'.next (e.f i)) := by
  intro hi'
  obtain ⟨j, hj⟩ := e.mem_next hi'
  rw [← hj] at hi'
  have hij := (e.rel_iff i j).mp hi'
  obtain rfl := c.next_eq' hij
  exact hi hij

variable [DecidableRel c.Rel] [DecidableRel c'.Rel]

/-- The degreewise comparison between restricting a homotopy cofiber and taking the
homotopy cofiber after restriction. The truncation hypothesis ensures that an outgoing
edge from a degree in the image stays in the image. -/
noncomputable def restrictionComponentIso (i : ι) :
    ((homotopyCofiber φ).restriction e).X i ≅
      (homotopyCofiber (HomologicalComplex.restrictionMap φ e)).X i := by
  by_cases hi : c.Rel i (c.next i)
  · exact
      ((homotopyCofiber φ).restrictionXIso e rfl) ≪≫
        XIsoBiprod φ (e.f i) (e.f (c.next i)) (e.rel hi) ≪≫
        biprod.mapIso
          (F.restrictionXIso e rfl).symm
          (G.restrictionXIso e rfl).symm ≪≫
        (XIsoBiprod (HomologicalComplex.restrictionMap φ e)
          i (c.next i) hi).symm
  · exact
      ((homotopyCofiber φ).restrictionXIso e rfl) ≪≫
        XIso φ (e.f i) (not_rel_next_of_not_rel_next e i hi) ≪≫
        (G.restrictionXIso e rfl).symm ≪≫
        (XIso (HomologicalComplex.restrictionMap φ e) i hi).symm

/-- The restriction comparison carries the first cofiber projection to the restricted first
projection. -/
@[reassoc]
lemma restrictionComponentIso_hom_fstX (i j : ι) (hij : c.Rel i j) :
    (restrictionComponentIso φ e i).hom ≫
        fstX (HomologicalComplex.restrictionMap φ e) i j hij =
      ((homotopyCofiber φ).restrictionXIso e rfl).hom ≫
        fstX φ (e.f i) (e.f j) (e.rel hij) ≫
        (F.restrictionXIso e rfl).inv := by
  obtain rfl := c.next_eq' hij
  unfold restrictionComponentIso
  rw [dite_eq_left hij]
  rw [fstX, ← Category.assoc]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_assoc]
  rw [biprod.mapIso_hom, biprod.map_fst]
  rw [fstX]
  simp only [Iso.symm_hom, Category.assoc]

/-- The restriction comparison carries the second cofiber projection to the restricted second
projection. -/
@[reassoc]
lemma restrictionComponentIso_hom_sndX (i : ι) :
    (restrictionComponentIso φ e i).hom ≫
        sndX (HomologicalComplex.restrictionMap φ e) i =
      ((homotopyCofiber φ).restrictionXIso e rfl).hom ≫
        sndX φ (e.f i) ≫
        (G.restrictionXIso e rfl).inv := by
  unfold restrictionComponentIso
  split_ifs with hi
  · rw [sndX_eq_XIsoBiprod
      (HomologicalComplex.restrictionMap φ e) i (c.next i) hi]
    rw [sndX_eq_XIsoBiprod φ (e.f i) (e.f (c.next i)) (e.rel hi)]
    rw [← Category.assoc]
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Iso.inv_hom_id_assoc]
    rw [biprod.mapIso_hom, biprod.map_snd]
    simp only [Iso.symm_hom]
  · simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
    dsimp only [sndX]
    rw [dite_eq_right hi, dite_eq_right (not_rel_next_of_not_rel_next e i hi)]
    simp

/-- Restriction along an outgoing-closed embedding commutes with homotopy cofibers. -/
noncomputable def restrictionIso :
    (homotopyCofiber φ).restriction e ≅
      homotopyCofiber (HomologicalComplex.restrictionMap φ e) :=
  HomologicalComplex.Hom.isoOfComponents
    (restrictionComponentIso φ e) (by
      intro i j hij
      by_cases hj : c.Rel j (c.next j)
      · apply ext_to_X (HomologicalComplex.restrictionMap φ e)
          j (c.next j) hj
        · rw [HomologicalComplex.homotopyCofiber_d, Category.assoc,
            d_fstX (HomologicalComplex.restrictionMap φ e)
              i j (c.next j) hij hj]
          simp only [CategoryTheory.Preadditive.comp_neg,
            restrictionComponentIso_hom_fstX_assoc,
            restrictionComponentIso_hom_fstX, Category.assoc]
          suffices h :
              -fstX φ (e.f i) (e.f j) (e.rel hij) ≫
                  F.d (e.f j) (e.f (c.next j)) =
                homotopyCofiber.d φ (e.f i) (e.f j) ≫
                  fstX φ (e.f j) (e.f (c.next j)) (e.rel hj) by
            convert h using 1 <;> simp [HomologicalComplex.restriction]
            all_goals congr 1
          exact (d_fstX φ (e.f i) (e.f j) (e.f (c.next j))
            (e.rel hij) (e.rel hj)).symm
        · rw [HomologicalComplex.homotopyCofiber_d, Category.assoc,
            d_sndX (HomologicalComplex.restrictionMap φ e) i j hij]
          simp only [CategoryTheory.Preadditive.comp_add,
            restrictionComponentIso_hom_fstX_assoc,
            restrictionComponentIso_hom_sndX_assoc,
            restrictionComponentIso_hom_sndX, Category.assoc]
          suffices h :
              fstX φ (e.f i) (e.f j) (e.rel hij) ≫ φ.f (e.f j) +
                  sndX φ (e.f i) ≫ G.d (e.f i) (e.f j) =
                homotopyCofiber.d φ (e.f i) (e.f j) ≫
                  sndX φ (e.f j) by
            convert h using 1 <;> simp [HomologicalComplex.restriction]
            all_goals congr 1
          exact (d_sndX φ (e.f i) (e.f j) (e.rel hij)).symm
      · apply ext_to_X' (HomologicalComplex.restrictionMap φ e) j hj
        rw [HomologicalComplex.homotopyCofiber_d, Category.assoc,
          d_sndX (HomologicalComplex.restrictionMap φ e) i j hij]
        simp only [CategoryTheory.Preadditive.comp_add,
          restrictionComponentIso_hom_fstX_assoc,
          restrictionComponentIso_hom_sndX_assoc,
          restrictionComponentIso_hom_sndX, Category.assoc]
        suffices h :
            fstX φ (e.f i) (e.f j) (e.rel hij) ≫ φ.f (e.f j) +
                sndX φ (e.f i) ≫ G.d (e.f i) (e.f j) =
              homotopyCofiber.d φ (e.f i) (e.f j) ≫
                sndX φ (e.f j) by
          convert h using 1 <;> simp [HomologicalComplex.restriction]
          all_goals congr 1
        exact (d_sndX φ (e.f i) (e.f j) (e.rel hij)).symm)

/-- The first cofiber inclusion is preserved by the restriction comparison. -/
@[reassoc]
lemma inlX_restrictionIso_hom_f (i j : ι) (hji : c.Rel j i) :
    inlX φ (e.f i) (e.f j) (e.rel hji) ≫
        ((homotopyCofiber φ).restrictionXIso e rfl).inv ≫
          (restrictionIso φ e).hom.f j =
      (F.restrictionXIso e rfl).inv ≫
        inlX (HomologicalComplex.restrictionMap φ e) i j hji := by
  change inlX φ (e.f i) (e.f j) (e.rel hji) ≫
      ((homotopyCofiber φ).restrictionXIso e rfl).inv ≫
        (restrictionComponentIso φ e j).hom = _
  obtain rfl := c.next_eq' hji
  unfold restrictionComponentIso
  rw [dite_eq_left hji]
  simp only [Iso.trans_hom, Iso.inv_hom_id_assoc]
  rw [inlX_XIsoBiprod_hom_assoc]
  rw [biprod.mapIso_hom, biprod.inl_map_assoc]
  simp only [Iso.symm_hom, inl_XIsoBiprod_inv]

/-- The target inclusion is preserved by the restriction comparison. -/
@[reassoc]
lemma inrX_restrictionIso_hom_f (i : ι) :
    inrX φ (e.f i) ≫
        ((homotopyCofiber φ).restrictionXIso e rfl).inv ≫
          (restrictionIso φ e).hom.f i =
      (G.restrictionXIso e rfl).inv ≫
        inrX (HomologicalComplex.restrictionMap φ e) i := by
  change inrX φ (e.f i) ≫
      ((homotopyCofiber φ).restrictionXIso e rfl).inv ≫
        (restrictionComponentIso φ e i).hom = _
  unfold restrictionComponentIso
  split_ifs with hi
  · simp only [Iso.trans_hom, Iso.inv_hom_id_assoc]
    rw [inrX_XIsoBiprod_hom_assoc]
    rw [biprod.mapIso_hom, biprod.inr_map_assoc]
    simp only [Iso.symm_hom, inr_XIsoBiprod_inv]
  · dsimp only [Iso.trans_hom, Iso.symm_hom]
    have hi' := not_rel_next_of_not_rel_next e i hi
    rw [show inrX φ (e.f i) = (XIso φ (e.f i) hi').inv by
      simp [inrX, hi']]
    rw [show inrX (HomologicalComplex.restrictionMap φ e) i =
        (XIso (HomologicalComplex.restrictionMap φ e) i hi).inv by
      simp [inrX, hi]]
    simp only [Iso.inv_hom_id_assoc]

end Object

variable [DecidableRel c.Rel] [DecidableRel c'.Rel]

section Naturality

variable (e : c.Embedding c') [e.IsTruncGE]
variable (hc : ∀ j : ι, ∃ i, c.Rel i j)
variable (hc' : ∀ j : ι', ∃ i, c'.Rel i j)

/-- Naturality of the homotopy-cofiber restriction comparison. -/
@[reassoc]
theorem restrictionIso_naturality
    {φ ψ : Arrow (HomologicalComplex C c')} (a : φ ⟶ ψ) :
    HomologicalComplex.restrictionMap
        (mapArrowHom φ.hom ψ.hom hc'
          (Arrow.homMk' a.left a.right (w := a.w))) e ≫
        (restrictionIso ψ.hom e).hom =
      (restrictionIso φ.hom e).hom ≫
        mapArrowHom
          (HomologicalComplex.restrictionMap φ.hom e)
          (HomologicalComplex.restrictionMap ψ.hom e) hc
          ((e.restrictionFunctor C).mapArrow.map a) := by
  let a' : Arrow.mk φ.hom ⟶ Arrow.mk ψ.hom :=
    Arrow.homMk' a.left a.right (w := a.w)
  let ae :
      Arrow.mk (HomologicalComplex.restrictionMap φ.hom e) ⟶
        Arrow.mk (HomologicalComplex.restrictionMap ψ.hom e) :=
    Arrow.homMk'
      (HomologicalComplex.restrictionMap a.left e)
      (HomologicalComplex.restrictionMap a.right e)
      (w := by
        ext i
        exact congrArg (fun k ↦ k.f (e.f i)) a.w)
  ext i
  change (HomologicalComplex.restrictionMap
      (mapArrowHom φ.hom ψ.hom hc' a') e).f i ≫
      (restrictionIso ψ.hom e).hom.f i =
    (restrictionIso φ.hom e).hom.f i ≫
      (mapArrowHom
        (HomologicalComplex.restrictionMap φ.hom e)
        (HomologicalComplex.restrictionMap ψ.hom e) hc ae).f i
  apply (cancel_epi
    ((homotopyCofiber φ.hom).restrictionXIso e rfl).inv).1
  by_cases hi : c.Rel i (c.next i)
  · apply ext_from_X φ.hom (e.f (c.next i)) (e.f i) (e.rel hi)
    · rw [HomologicalComplex.restrictionMap_f'
        (mapArrowHom φ.hom ψ.hom hc' a') e rfl]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [inlX_mapArrowHom_assoc hc' a']
      rw [inlX_restrictionIso_hom_f ψ.hom e (c.next i) i hi]
      rw [inlX_restrictionIso_hom_f_assoc φ.hom e (c.next i) i hi]
      rw [inlX_mapArrowHom hc
        ae (c.next i) i hi]
      simp [a', ae, HomologicalComplex.restriction,
        HomologicalComplex.restrictionMap]
    · rw [HomologicalComplex.restrictionMap_f'
        (mapArrowHom φ.hom ψ.hom hc' a') e rfl]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [inrX_mapArrowHom_assoc hc' a']
      rw [inrX_restrictionIso_hom_f ψ.hom e i]
      rw [inrX_restrictionIso_hom_f_assoc φ.hom e i]
      rw [inrX_mapArrowHom hc ae i]
      simp [a', ae, HomologicalComplex.restriction,
        HomologicalComplex.restrictionMap]
  · apply ext_from_X' φ.hom (e.f i)
      (not_rel_next_of_not_rel_next e i hi)
    rw [HomologicalComplex.restrictionMap_f'
      (mapArrowHom φ.hom ψ.hom hc' a') e rfl]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [inrX_mapArrowHom_assoc hc' a']
    rw [inrX_restrictionIso_hom_f ψ.hom e i]
    rw [inrX_restrictionIso_hom_f_assoc φ.hom e i]
    rw [inrX_mapArrowHom hc ae i]
    simp [a', ae, HomologicalComplex.restriction,
      HomologicalComplex.restrictionMap]

/-- Homotopy cofibers commute naturally with restriction along an outgoing-closed
embedding of complex shapes. -/
noncomputable def restrictionNatIso :
    homotopyCofiberFunctor hc' ⋙ e.restrictionFunctor C ≅
      (e.restrictionFunctor C).mapArrow ⋙ homotopyCofiberFunctor hc :=
  NatIso.ofComponents
    (fun φ ↦ restrictionIso φ.hom e)
    (fun a ↦ restrictionIso_naturality e hc hc' a)

/-- The forward component of `restrictionNatIso`. -/
@[simp]
lemma restrictionNatIso_hom_app (φ : Arrow (HomologicalComplex C c')) :
    (restrictionNatIso e hc hc').hom.app φ = (restrictionIso φ.hom e).hom :=
  rfl

/-- The inverse component of `restrictionNatIso`. -/
@[simp]
lemma restrictionNatIso_inv_app (φ : Arrow (HomologicalComplex C c')) :
    (restrictionNatIso e hc hc').inv.app φ = (restrictionIso φ.hom e).inv :=
  rfl

/-- Restriction comparison commutes with the universal map attached to a short complex. -/
@[reassoc]
theorem restrictionIso_hom_descShortComplex
    (S : ShortComplex (HomologicalComplex C c')) :
    (restrictionIso S.f e).hom ≫
        descShortComplex (S.map (e.restrictionFunctor C)) =
      HomologicalComplex.restrictionMap (descShortComplex S) e := by
  let hMap : _root_.Homotopy
      (HomologicalComplex.restrictionMap S.f e ≫
        HomologicalComplex.restrictionMap S.g e) 0 :=
    _root_.Homotopy.ofEq (by
      rw [← HomologicalComplex.restrictionMap_comp, S.zero]
      rfl)
  let hOrig : _root_.Homotopy (S.f ≫ S.g) 0 :=
    _root_.Homotopy.ofEq S.zero
  ext i
  apply (cancel_epi
    ((homotopyCofiber S.f).restrictionXIso e rfl).inv).1
  by_cases hi : c.Rel i (c.next i)
  · apply ext_from_X S.f (e.f (c.next i)) (e.f i) (e.rel hi)
    · change inlX S.f (e.f (c.next i)) (e.f i) (e.rel hi) ≫
          ((homotopyCofiber S.f).restrictionXIso e rfl).inv ≫
            (restrictionIso S.f e).hom.f i ≫
          (desc (HomologicalComplex.restrictionMap S.f e)
            (HomologicalComplex.restrictionMap S.g e) hMap).f i =
        inlX S.f (e.f (c.next i)) (e.f i) (e.rel hi) ≫
          ((homotopyCofiber S.f).restrictionXIso e rfl).inv ≫
            (HomologicalComplex.restrictionMap
              (desc S.f S.g hOrig) e).f i
      rw [inlX_restrictionIso_hom_f_assoc
        S.f e (c.next i) i hi]
      rw [inlX_desc_f
        (φ := HomologicalComplex.restrictionMap S.f e)
        (α := HomologicalComplex.restrictionMap S.g e)
        (hα := hMap) (c.next i) i hi]
      rw [HomologicalComplex.restrictionMap_f' (desc S.f S.g hOrig) e rfl]
      simp only [Iso.inv_hom_id_assoc]
      rw [inlX_desc_f_assoc
        (φ := S.f) (α := S.g) (hα := hOrig)
        (e.f (c.next i)) (e.f i) (e.rel hi)]
      simp only [restrictionXIso_rfl, Iso.refl_inv]
      exact comp_zero.trans zero_comp.symm
    · change inrX S.f (e.f i) ≫
          ((homotopyCofiber S.f).restrictionXIso e rfl).inv ≫
            (restrictionIso S.f e).hom.f i ≫
          (desc (HomologicalComplex.restrictionMap S.f e)
            (HomologicalComplex.restrictionMap S.g e) hMap).f i =
        inrX S.f (e.f i) ≫
          ((homotopyCofiber S.f).restrictionXIso e rfl).inv ≫
            (HomologicalComplex.restrictionMap
              (desc S.f S.g hOrig) e).f i
      rw [inrX_restrictionIso_hom_f_assoc]
      rw [inrX_desc_f]
      rw [HomologicalComplex.restrictionMap_f' (desc S.f S.g hOrig) e rfl]
      rw [HomologicalComplex.restrictionMap_f' S.g e rfl]
      simp only [Iso.inv_hom_id_assoc]
      rw [inrX_desc_f_assoc]
  · apply ext_from_X' S.f (e.f i)
      (not_rel_next_of_not_rel_next e i hi)
    change inrX S.f (e.f i) ≫
        ((homotopyCofiber S.f).restrictionXIso e rfl).inv ≫
          (restrictionIso S.f e).hom.f i ≫
        (desc (HomologicalComplex.restrictionMap S.f e)
          (HomologicalComplex.restrictionMap S.g e) hMap).f i =
      inrX S.f (e.f i) ≫
        ((homotopyCofiber S.f).restrictionXIso e rfl).inv ≫
          (HomologicalComplex.restrictionMap
            (desc S.f S.g hOrig) e).f i
    rw [inrX_restrictionIso_hom_f_assoc]
    rw [inrX_desc_f]
    rw [HomologicalComplex.restrictionMap_f' (desc S.f S.g hOrig) e rfl]
    rw [HomologicalComplex.restrictionMap_f' S.g e rfl]
    simp only [Iso.inv_hom_id_assoc]
    rw [inrX_desc_f_assoc]

end Naturality

end HomologicalComplex.homotopyCofiber
