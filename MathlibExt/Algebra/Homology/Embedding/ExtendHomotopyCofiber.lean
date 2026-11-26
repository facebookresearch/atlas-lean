/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy
public import MathlibExt.Algebra.Homology.HomotopyCofiber
public import MathlibExt.Algebra.Homology.HomotopyCofiberProjection

/-!
# Homotopy cofibers and extension by zero

For an incoming-closed embedding of complex shapes, extension by zero
commutes with homotopy cofibers. On a retained outgoing edge i→j, the
comparison identifies the source coordinate F_j and target coordinate G_i.
At a source boundary it discards an ambient source coordinate that is
zero, and outside the image all terms are zero.

If every degree has a predecessor, the canonical null-homotopies identify
the forward isomorphism with the universal comparison. With this condition
in both shapes, the comparisons form a natural isomorphism of cofiber
functors. Short-complex descent maps are compatible with the comparison.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace HomologicalComplex.homotopyCofiber

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C]
variable {ι : Type w} {ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

section Object

variable {F G : HomologicalComplex C c} (φ : F ⟶ G)
variable (e : c.Embedding c') [e.IsTruncLE]
variable (hc : ∀ j : ι, ∃ i, c.Rel i j)

/--
Let e:c→c' be a relation-reflecting embedding of complex shapes whose image is closed under
incoming differentials (IsTruncLE). If c'.Rel i' j' and i' lies outside the image, then j'
also lies outside the image; otherwise incoming closure would put i' in the image.
-/
lemma not_mem_of_rel_of_not_mem_source
    {i' j' : ι'} (hij : c'.Rel i' j')
    (hi : ∀ i, e.f i ≠ i') : ∀ j, e.f j ≠ j' := by
  intro j hj
  rw [← hj] at hij
  obtain ⟨i, hi'⟩ := e.mem_prev hij
  exact hi i hi'

/--
Let e:c→c' be a relation-reflecting embedding of complex shapes whose image is closed under
incoming differentials (IsTruncLE). If i has no outgoing edge in c but e(i) has an outgoing
edge in c', the target c'.next(e(i)) is outside the image of e.
-/
lemma not_mem_next_of_not_rel_next (i : ι)
    (hi : ¬ c.Rel i (c.next i))
    (hi' : c'.Rel (e.f i) (c'.next (e.f i))) :
    ∀ j, e.f j ≠ c'.next (e.f i) := by
  intro j hj
  rw [← hj] at hi'
  have hij := (e.rel_iff i j).mp hi'
  obtain rfl := c.next_eq' hij
  exact hi hij

variable [DecidableRel c.Rel]

/--
Let C be preadditive with a zero object and binary biproducts, let φ:F→G be a c-complex map,
and let e:c→c' be incoming-closed and relation-reflecting. Assume c.Rel is decidable and every
c-degree has a predecessor. Extending the canonical null-homotopy of φ≫inr_φ gives a homotopy
from extend(φ)≫extend(inr_φ) to zero.
-/
noncomputable def extendInrCompHomotopy :
    _root_.Homotopy
      (HomologicalComplex.extendMap φ e ≫
        HomologicalComplex.extendMap (inr φ) e) 0 :=
  (Homotopy.ofEq
      (HomologicalComplex.extendMap_comp φ (inr φ) e).symm).trans
    (((inrCompHomotopy φ hc).extend e).trans
      (Homotopy.ofEq
        (HomologicalComplex.extendMap_zero
          (K := F) (L := homotopyCofiber φ) e)))

/--
Let C be preadditive with a zero object and binary biproducts, φ:F→G a c-complex map, and e an
incoming-closed embedding. Assume c.Rel is decidable and every c-degree has a predecessor. For
c.Rel j i, the extended null-homotopy component at e(i)→e(j) is the original source-summand
inclusion F_i→H(φ)_j, conjugated by the canonical extension term identifications.
-/
lemma extendInrCompHomotopy_hom (i j : ι) (hji : c.Rel j i) :
    (extendInrCompHomotopy φ e hc).hom (e.f i) (e.f j) =
      (F.extendXIso e rfl).hom ≫
        inlX φ i j hji ≫
        ((homotopyCofiber φ).extendXIso e rfl).inv := by
  simp only [extendInrCompHomotopy, Homotopy.trans_hom,
    Homotopy.ofEq_hom, Pi.zero_apply, zero_add, add_zero]
  rw [Homotopy.extend_hom_eq _ e rfl rfl]
  rw [inrCompHomotopy_hom]

variable [DecidableRel c'.Rel]

/--
Let C be preadditive with a zero object and binary biproducts. Let φ:F→G be a morphism of
c-complexes and e:c→c' an incoming-closed, relation-reflecting embedding. Write e_* for
extension by zero and H(φ) for the homotopy cofiber. Assume the relations of c and c' are
decidable. Assume every degree of c has an incoming edge. The extended target inclusion
e_*G→e_*H(φ), together with the extended null-homotopy of e_*φ, defines the canonical
comparison H(e_*φ)→e_*H(φ).
-/
noncomputable def extendComparison :
    homotopyCofiber (HomologicalComplex.extendMap φ e) ⟶
      (homotopyCofiber φ).extend e :=
  desc (HomologicalComplex.extendMap φ e)
    (HomologicalComplex.extendMap (inr φ) e)
    (extendInrCompHomotopy φ e hc)

/--
Let C be preadditive with a zero object and binary biproducts. Let φ:F→G be a morphism of
c-complexes and e:c→c' an incoming-closed, relation-reflecting embedding. Write e_* for
extension by zero and H(φ) for the homotopy cofiber. Assume the relations of c and c' are
decidable. At an image degree e(i), the canonical comparison identifies H(e_*φ)_{e(i)} with
(e_*H(φ))_{e(i)}, using the original source/target cofiber summands and the extension term
isomorphisms.
-/
noncomputable def extendComponentIsoImage (i : ι) :
    (homotopyCofiber (HomologicalComplex.extendMap φ e)).X (e.f i) ≅
      ((homotopyCofiber φ).extend e).X (e.f i) := by
  by_cases hi : c.Rel i (c.next i)
  · exact
        XIsoBiprod (HomologicalComplex.extendMap φ e)
            (e.f i) (e.f (c.next i)) (e.rel hi) ≪≫
          biprod.mapIso
            (F.extendXIso e rfl)
            (G.extendXIso e rfl) ≪≫
          (XIsoBiprod φ i (c.next i) hi).symm ≪≫
          ((homotopyCofiber φ).extendXIso e rfl).symm
  · by_cases hi' : c'.Rel (e.f i) (c'.next (e.f i))
    · let hF : IsZero ((F.extend e).X (c'.next (e.f i))) :=
          F.isZero_extend_X e _
            (not_mem_next_of_not_rel_next e i hi hi')
      exact
          XIsoBiprod (HomologicalComplex.extendMap φ e)
              (e.f i) (c'.next (e.f i)) hi' ≪≫
            (isoZeroBiprod hF).symm ≪≫
            G.extendXIso e rfl ≪≫
            (XIso φ i hi).symm ≪≫
            ((homotopyCofiber φ).extendXIso e rfl).symm
    · exact
          XIso (HomologicalComplex.extendMap φ e) (e.f i) hi' ≪≫
            G.extendXIso e rfl ≪≫
            (XIso φ i hi).symm ≪≫
            ((homotopyCofiber φ).extendXIso e rfl).symm

/--
Let C be preadditive with a zero object and binary biproducts. Let φ:F→G be a morphism of
c-complexes and e:c→c' an incoming-closed, relation-reflecting embedding. Write e_* for
extension by zero and H(φ) for the homotopy cofiber. Assume the relations of c and c' are
decidable. For i' and a selected preimage i with e(i)=i', the retained-degree comparison gives
H(e_*φ)_{i'}≅(e_*H(φ))_{i'}, transporting the same source and target cofiber coordinates along
that equality.
-/
noncomputable def extendComponentIsoPreimage {i' : ι'}
    (p : {i // e.f i = i'}) :
    (homotopyCofiber (HomologicalComplex.extendMap φ e)).X i' ≅
      ((homotopyCofiber φ).extend e).X i' :=
  eqToIso (by rw [p.property]) ≪≫
    extendComponentIsoImage φ e p.1 ≪≫
      eqToIso (by rw [p.property])

/--
Let C be preadditive with a zero object and binary biproducts. Let φ:F→G be a morphism of
c-complexes and e:c→c' an incoming-closed, relation-reflecting embedding. Write e_* for
extension by zero and H(φ) for the homotopy cofiber. Assume the relations of c and c' are
decidable. At every c'-degree i', there is a canonical isomorphism
H(e_*φ)_{i'}≅(e_*H(φ))_{i'}. Retained degrees use the original cofiber coordinates; outside
the image both sides are zero objects.
-/
noncomputable def extendComponentIso (i' : ι') :
    (homotopyCofiber (HomologicalComplex.extendMap φ e)).X i' ≅
      ((homotopyCofiber φ).extend e).X i' := by
  by_cases hmem : ∃ i, e.f i = i'
  · exact extendComponentIsoPreimage φ e ⟨hmem.choose, hmem.choose_spec⟩
  · have hmem' : ∀ i, e.f i ≠ i' := by
      simpa using hmem
    let hG : IsZero ((G.extend e).X i') :=
      G.isZero_extend_X e i' hmem'
    let hF : ∀ j', c'.Rel i' j' → IsZero ((F.extend e).X j') := by
      intro j' hij
      exact F.isZero_extend_X e j'
        (not_mem_of_rel_of_not_mem_source e hij hmem')
    exact IsZero.iso
      (isZero_X (HomologicalComplex.extendMap φ e) i' hG hF)
      ((homotopyCofiber φ).isZero_extend_X e i' hmem')

/--
Let C be preadditive with a zero object and binary biproducts. Let φ:F→G be a morphism of
c-complexes and e:c→c' an incoming-closed, relation-reflecting embedding. Write e_* for
extension by zero and H(φ) for the homotopy cofiber. Assume the relations of c and c' are
decidable. For an outgoing edge i→j in c, the cofiber term at i is presented as F_j⊞G_i. At
e(i), the component comparison is the direct sum of the extension identifications on F_j and
G_i, followed by the inverse original cofiber presentation and inverse extension coordinate of
H(φ).
-/
lemma extendComponentIso_of_rel (i j : ι) (hij : c.Rel i j) :
    extendComponentIso φ e (e.f i) =
      XIsoBiprod (HomologicalComplex.extendMap φ e)
          (e.f i) (e.f j) (e.rel hij) ≪≫
        biprod.mapIso
          (F.extendXIso e rfl)
          (G.extendXIso e rfl) ≪≫
        (XIsoBiprod φ i j hij).symm ≪≫
        ((homotopyCofiber φ).extendXIso e rfl).symm := by
  obtain rfl := c.next_eq' hij
  unfold extendComponentIso
  rw [dite_eq_left ⟨i, rfl⟩]
  let h : ∃ k, e.f k = e.f i := ⟨i, rfl⟩
  let p : {k // e.f k = e.f i} := ⟨h.choose, h.choose_spec⟩
  change extendComponentIsoPreimage φ e p = _
  have hp : p = ⟨i, rfl⟩ := by
    apply Subtype.ext
    exact e.injective_f p.property
  rw [hp]
  simp [extendComponentIsoPreimage, extendComponentIsoImage, hij]

/--
Let C be preadditive with a zero object and binary biproducts. Let φ:F→G be a morphism of
c-complexes and e:c→c' an incoming-closed, relation-reflecting embedding. Write e_* for
extension by zero and H(φ) for the homotopy cofiber. Assume the relations of c and c' are
decidable. Suppose i has no outgoing source edge but e(i) has an outgoing ambient edge. Its
ambient successor is outside the image, so the extended source summand is zero. The component
isomorphism discards that zero summand and identifies the remaining G_i coordinate with the
original boundary cofiber term.
-/
lemma extendComponentIso_of_boundary (i : ι)
    (hi : ¬ c.Rel i (c.next i))
    (hi' : c'.Rel (e.f i) (c'.next (e.f i))) :
    extendComponentIso φ e (e.f i) =
      XIsoBiprod (HomologicalComplex.extendMap φ e)
          (e.f i) (c'.next (e.f i)) hi' ≪≫
        (isoZeroBiprod
          (F.isZero_extend_X e _
            (not_mem_next_of_not_rel_next e i hi hi'))).symm ≪≫
        G.extendXIso e rfl ≪≫
        (XIso φ i hi).symm ≪≫
        ((homotopyCofiber φ).extendXIso e rfl).symm := by
  unfold extendComponentIso
  rw [dite_eq_left ⟨i, rfl⟩]
  let h : ∃ k, e.f k = e.f i := ⟨i, rfl⟩
  let p : {k // e.f k = e.f i} := ⟨h.choose, h.choose_spec⟩
  change extendComponentIsoPreimage φ e p = _
  have hp : p = ⟨i, rfl⟩ := by
    apply Subtype.ext
    exact e.injective_f p.property
  rw [hp]
  simp [extendComponentIsoPreimage, extendComponentIsoImage, hi, hi']

/--
Let C be preadditive with a zero object and binary biproducts. Let φ:F→G be a morphism of
c-complexes and e:c→c' an incoming-closed, relation-reflecting embedding. Write e_* for
extension by zero and H(φ) for the homotopy cofiber. Assume the relations of c and c' are
decidable. If neither i nor e(i) has an outgoing edge, the cofiber terms are their target
G-coordinates. The comparison at e(i) is induced solely by the canonical extension
identification of G_i.
-/
lemma extendComponentIso_of_no_rel (i : ι)
    (hi : ¬ c.Rel i (c.next i))
    (hi' : ¬ c'.Rel (e.f i) (c'.next (e.f i))) :
    extendComponentIso φ e (e.f i) =
      XIso (HomologicalComplex.extendMap φ e) (e.f i) hi' ≪≫
        G.extendXIso e rfl ≪≫
        (XIso φ i hi).symm ≪≫
        ((homotopyCofiber φ).extendXIso e rfl).symm := by
  unfold extendComponentIso
  rw [dite_eq_left ⟨i, rfl⟩]
  let h : ∃ k, e.f k = e.f i := ⟨i, rfl⟩
  let p : {k // e.f k = e.f i} := ⟨h.choose, h.choose_spec⟩
  change extendComponentIsoPreimage φ e p = _
  have hp : p = ⟨i, rfl⟩ := by
    apply Subtype.ext
    exact e.injective_f p.property
  rw [hp]
  simp [extendComponentIsoPreimage, extendComponentIsoImage, hi, hi']

/--
Let C be preadditive with a zero object and binary biproducts. Let φ:F→G be a morphism of
c-complexes and e:c→c' an incoming-closed, relation-reflecting embedding. Write e_* for
extension by zero and H(φ) for the homotopy cofiber. Assume the relations of c and c' are
decidable. For c.Rel i j, let θ be the component comparison at e(i) and γ the extension
identification of H(φ)_i. Then θ.hom≫γ.hom≫pr_F equals the extended cofiber's projection to
(e_*F)_{e(j)} followed by its identification with F_j.
-/
@[reassoc]
lemma extendComponentIso_hom_extendXIso_fstX
    (i j : ι) (hij : c.Rel i j) :
    (extendComponentIso φ e (e.f i)).hom ≫
        ((homotopyCofiber φ).extendXIso e rfl).hom ≫
        fstX φ i j hij =
      fstX (HomologicalComplex.extendMap φ e)
          (e.f i) (e.f j) (e.rel hij) ≫
        (F.extendXIso e rfl).hom := by
  rw [extendComponentIso_of_rel φ e i j hij]
  dsimp only [Iso.trans_hom, Iso.symm_hom]
  simp [fstX, Category.assoc]

/--
Let C be preadditive with a zero object and binary biproducts. Let φ:F→G be a morphism of
c-complexes and e:c→c' an incoming-closed, relation-reflecting embedding. Write e_* for
extension by zero and H(φ) for the homotopy cofiber. Assume the relations of c and c' are
decidable. At e(i), let θ be the component comparison and γ identify the extended original
cofiber term with H(φ)_i. The target-coordinate projection satisfies θ.hom≫γ.hom≫pr_G =
pr_{e_*G}≫α_G, with α_G the extension identification of G_i.
-/
@[reassoc]
lemma extendComponentIso_hom_extendXIso_sndX (i : ι) :
    (extendComponentIso φ e (e.f i)).hom ≫
        ((homotopyCofiber φ).extendXIso e rfl).hom ≫
        sndX φ i =
      sndX (HomologicalComplex.extendMap φ e) (e.f i) ≫
        (G.extendXIso e rfl).hom := by
  by_cases hi : c.Rel i (c.next i)
  · rw [extendComponentIso_of_rel φ e i (c.next i) hi]
    dsimp only [Iso.trans_hom, Iso.symm_hom]
    rw [sndX_eq_XIsoBiprod φ i (c.next i) hi]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [biprod.mapIso_hom, biprod.map_snd]
    rw [sndX_eq_XIsoBiprod
      (HomologicalComplex.extendMap φ e)
      (e.f i) (e.f (c.next i)) (e.rel hi)]
    simp only [Category.assoc]
  · by_cases hi' : c'.Rel (e.f i) (c'.next (e.f i))
    · rw [extendComponentIso_of_boundary φ e i hi hi']
      dsimp only [Iso.trans_hom, Iso.symm_hom]
      simp [sndX, hi, hi', isoZeroBiprod]
    · rw [extendComponentIso_of_no_rel φ e i hi hi']
      dsimp only [Iso.trans_hom, Iso.symm_hom]
      simp [sndX, hi, hi']

/--
Let C be preadditive with a zero object and binary biproducts. Let φ:F→G be a morphism of
c-complexes and e:c→c' an incoming-closed, relation-reflecting embedding. Write e_* for
extension by zero and H(φ) for the homotopy cofiber. Assume the relations of c and c' are
decidable. For c.Rel j i, the source-coordinate inclusion (e_*F)_{e(i)}→H(e_*φ)_{e(j)}
followed by the component comparison equals the identification with F_i, its original
inclusion into H(φ)_j, and inverse extension identification of that term.
-/
@[reassoc]
lemma inlX_extendComponentIso_hom (i j : ι) (hji : c.Rel j i) :
    inlX (HomologicalComplex.extendMap φ e)
        (e.f i) (e.f j) (e.rel hji) ≫
        (extendComponentIso φ e (e.f j)).hom =
      (F.extendXIso e rfl).hom ≫
        inlX φ i j hji ≫
        ((homotopyCofiber φ).extendXIso e rfl).inv := by
  rw [extendComponentIso_of_rel φ e j i hji]
  dsimp only [Iso.trans_hom]
  rw [inlX_XIsoBiprod_hom_assoc]
  rw [biprod.mapIso_hom, biprod.inl_map_assoc]
  simp only [Iso.symm_hom]
  rw [← inl_XIsoBiprod_inv φ i j hji]
  simp only [Category.assoc]

/--
Let C be preadditive with a zero object and binary biproducts. Let φ:F→G be a morphism of
c-complexes and e:c→c' an incoming-closed, relation-reflecting embedding. Write e_* for
extension by zero and H(φ) for the homotopy cofiber. Assume the relations of c and c' are
decidable. At e(i), the target inclusion (e_*G)_{e(i)}→H(e_*φ)_{e(i)} followed by the
component comparison equals the identification with G_i, its original target inclusion, and
inverse extension identification of H(φ)_i.
-/
@[reassoc]
lemma inrX_extendComponentIso_hom (i : ι) :
    inrX (HomologicalComplex.extendMap φ e) (e.f i) ≫
        (extendComponentIso φ e (e.f i)).hom =
      (G.extendXIso e rfl).hom ≫
        inrX φ i ≫
        ((homotopyCofiber φ).extendXIso e rfl).inv := by
  by_cases hi : c.Rel i (c.next i)
  · rw [extendComponentIso_of_rel φ e i (c.next i) hi]
    dsimp only [Iso.trans_hom]
    rw [inrX_XIsoBiprod_hom_assoc]
    rw [biprod.mapIso_hom, biprod.inr_map_assoc]
    simp only [Iso.symm_hom]
    rw [← inr_XIsoBiprod_inv φ (c.next i) i hi]
    simp only [Category.assoc]
  · by_cases hi' : c'.Rel (e.f i) (c'.next (e.f i))
    · rw [extendComponentIso_of_boundary φ e i hi hi']
      dsimp only [Iso.trans_hom]
      rw [inrX_XIsoBiprod_hom_assoc]
      simp only [Iso.symm_hom, isoZeroBiprod, biprod.inr_snd_assoc]
      simp [inrX, hi]
    · rw [extendComponentIso_of_no_rel φ e i hi hi']
      dsimp only [Iso.trans_hom, Iso.symm_hom]
      simp [inrX, hi, hi']

private lemma extendComparison_f_eq (i' : ι') :
    (extendComparison φ e hc).f i' = (extendComponentIso φ e i').hom := by
  by_cases hmem : ∃ i, e.f i = i'
  · obtain ⟨i, rfl⟩ := hmem
    by_cases hi : c.Rel i (c.next i)
    · apply ext_from_X (HomologicalComplex.extendMap φ e)
        (e.f (c.next i)) (e.f i) (e.rel hi)
      · calc
          _ = (extendInrCompHomotopy φ e hc).hom
              (e.f (c.next i)) (e.f i) :=
            inlX_desc_f _ _ (extendInrCompHomotopy φ e hc)
              _ _ (e.rel hi)
          _ = (F.extendXIso e rfl).hom ≫
                inlX φ (c.next i) i hi ≫
                ((homotopyCofiber φ).extendXIso e rfl).inv :=
            extendInrCompHomotopy_hom φ e hc (c.next i) i hi
          _ = _ := by
            rw [extendComponentIso_of_rel φ e i (c.next i) hi]
            dsimp only [Iso.trans_hom]
            rw [inlX_XIsoBiprod_hom_assoc]
            rw [biprod.mapIso_hom, biprod.inl_map_assoc]
            simp only [Iso.symm_hom]
            rw [← inl_XIsoBiprod_inv φ (c.next i) i hi]
            simp only [Category.assoc]
      · calc
          _ = (HomologicalComplex.extendMap (inr φ) e).f (e.f i) :=
            inrX_desc_f _ _ (extendInrCompHomotopy φ e hc) _
          _ = (G.extendXIso e rfl).hom ≫
                (inr φ).f i ≫
                ((homotopyCofiber φ).extendXIso e rfl).inv :=
            HomologicalComplex.extendMap_f _ e rfl
          _ = _ := by
            rw [extendComponentIso_of_rel φ e i (c.next i) hi]
            dsimp only [Iso.trans_hom]
            rw [inrX_XIsoBiprod_hom_assoc]
            rw [biprod.mapIso_hom, biprod.inr_map_assoc]
            simp only [Iso.symm_hom]
            rw [inr_f]
            rw [← inr_XIsoBiprod_inv φ (c.next i) i hi]
            simp only [Category.assoc]
    · by_cases hi' : c'.Rel (e.f i) (c'.next (e.f i))
      · apply ext_from_X (HomologicalComplex.extendMap φ e)
          (c'.next (e.f i)) (e.f i) hi'
        · exact (F.isZero_extend_X e _
            (not_mem_next_of_not_rel_next e i hi hi')).eq_of_src _ _
        · calc
            _ = (HomologicalComplex.extendMap (inr φ) e).f (e.f i) :=
              inrX_desc_f _ _ (extendInrCompHomotopy φ e hc) _
            _ = (G.extendXIso e rfl).hom ≫
                  (inr φ).f i ≫
                  ((homotopyCofiber φ).extendXIso e rfl).inv :=
              HomologicalComplex.extendMap_f _ e rfl
            _ = _ := by
              rw [extendComponentIso_of_boundary φ e i hi hi']
              dsimp only [Iso.trans_hom]
              rw [inrX_XIsoBiprod_hom_assoc]
              simp only [Iso.symm_hom, isoZeroBiprod,
                biprod.inr_snd_assoc]
              rw [inr_f]
              simp only [inrX, dite_eq_right hi]
      · apply ext_from_X' (HomologicalComplex.extendMap φ e) (e.f i) hi'
        calc
          _ = (HomologicalComplex.extendMap (inr φ) e).f (e.f i) :=
            inrX_desc_f _ _ (extendInrCompHomotopy φ e hc) _
          _ = (G.extendXIso e rfl).hom ≫
                (inr φ).f i ≫
                ((homotopyCofiber φ).extendXIso e rfl).inv :=
            HomologicalComplex.extendMap_f _ e rfl
          _ = _ := by
            rw [extendComponentIso_of_no_rel φ e i hi hi']
            dsimp only [Iso.trans_hom, Iso.symm_hom]
            rw [inr_f]
            simp [inrX, hi, hi']
  · have hG : IsZero ((G.extend e).X i') :=
      G.isZero_extend_X e i' (by simpa using hmem)
    have hF : ∀ j', c'.Rel i' j' → IsZero ((F.extend e).X j') := by
      intro j' hij
      exact F.isZero_extend_X e j'
        (not_mem_of_rel_of_not_mem_source e hij (by simpa using hmem))
    exact (isZero_X (HomologicalComplex.extendMap φ e) i' hG hF).eq_of_src _ _

/--
Let C be preadditive with a zero object and binary biproducts. Let φ:F→G be a morphism of
c-complexes and e:c→c' an incoming-closed, relation-reflecting embedding. Write e_* for
extension by zero and H(φ) for the homotopy cofiber. Assume the relations of c and c' are
decidable. The degreewise comparisons form an isomorphism of complexes H(e_*φ)≅e_*H(φ),
including degrees outside the image and source boundary degrees.
-/
noncomputable def extendIso :
    homotopyCofiber (HomologicalComplex.extendMap φ e) ≅
      (homotopyCofiber φ).extend e :=
  HomologicalComplex.Hom.isoOfComponents
    (extendComponentIso φ e) (by
      intro i' j' hij
      by_cases hjmem : ∃ j, e.f j = j'
      · obtain ⟨j, rfl⟩ := hjmem
        obtain ⟨i, hi⟩ := e.mem_prev hij
        subst i'
        have hij' := (e.rel_iff i j).mp hij
        apply (cancel_mono
          ((homotopyCofiber φ).extendXIso e rfl).hom).1
        by_cases hj : c.Rel j (c.next j)
        · apply ext_to_X φ j (c.next j) hj
          · rw [HomologicalComplex.extend_d_eq
              (homotopyCofiber φ) e rfl rfl]
            simp only [Category.assoc, Iso.inv_hom_id_assoc]
            have hfst : (homotopyCofiber φ).d i j ≫
                fstX φ j (c.next j) hj =
              -fstX φ i j hij' ≫ F.d j (c.next j) := by
              exact d_fstX φ i j (c.next j) hij' hj
            rw [hfst]
            simp only [CategoryTheory.Preadditive.comp_neg,
              extendComponentIso_hom_extendXIso_fstX_assoc]
            slice_rhs 2 4 =>
              rw [extendComponentIso_hom_extendXIso_fstX
                φ e j (c.next j) hj]
            have hfstE :
                (homotopyCofiber (HomologicalComplex.extendMap φ e)).d
                    (e.f i) (e.f j) ≫
                  fstX (HomologicalComplex.extendMap φ e)
                    (e.f j) (e.f (c.next j)) (e.rel hj) =
                -fstX (HomologicalComplex.extendMap φ e)
                    (e.f i) (e.f j) hij ≫
                  (F.extend e).d (e.f j) (e.f (c.next j)) := by
              exact d_fstX (HomologicalComplex.extendMap φ e)
                (e.f i) (e.f j) (e.f (c.next j)) hij (e.rel hj)
            slice_rhs 1 2 => rw [hfstE]
            rw [F.extend_d_eq e rfl rfl]
            simp [Category.assoc]
          · rw [HomologicalComplex.extend_d_eq
              (homotopyCofiber φ) e rfl rfl]
            simp only [Category.assoc, Iso.inv_hom_id_assoc]
            have hsnd : (homotopyCofiber φ).d i j ≫ sndX φ j =
                fstX φ i j hij' ≫ φ.f j + sndX φ i ≫ G.d i j := by
              exact d_sndX φ i j hij'
            rw [hsnd]
            simp only [CategoryTheory.Preadditive.comp_add,
              extendComponentIso_hom_extendXIso_fstX_assoc,
              extendComponentIso_hom_extendXIso_sndX_assoc]
            slice_rhs 2 4 =>
              rw [extendComponentIso_hom_extendXIso_sndX φ e j]
            have hsndE :
                (homotopyCofiber (HomologicalComplex.extendMap φ e)).d
                    (e.f i) (e.f j) ≫
                  sndX (HomologicalComplex.extendMap φ e) (e.f j) =
                fstX (HomologicalComplex.extendMap φ e)
                      (e.f i) (e.f j) hij ≫
                    (HomologicalComplex.extendMap φ e).f (e.f j) +
                  sndX (HomologicalComplex.extendMap φ e) (e.f i) ≫
                    (G.extend e).d (e.f i) (e.f j) := by
              exact d_sndX (HomologicalComplex.extendMap φ e)
                (e.f i) (e.f j) hij
            slice_rhs 1 2 => rw [hsndE]
            rw [HomologicalComplex.extendMap_f φ e rfl]
            rw [G.extend_d_eq e rfl rfl]
            simp [CategoryTheory.Preadditive.add_comp, Category.assoc]
        · apply ext_to_X' φ j hj
          rw [HomologicalComplex.extend_d_eq
            (homotopyCofiber φ) e rfl rfl]
          simp only [Category.assoc, Iso.inv_hom_id_assoc]
          have hsnd : (homotopyCofiber φ).d i j ≫ sndX φ j =
              fstX φ i j hij' ≫ φ.f j + sndX φ i ≫ G.d i j := by
            exact d_sndX φ i j hij'
          rw [hsnd]
          simp only [CategoryTheory.Preadditive.comp_add,
            extendComponentIso_hom_extendXIso_fstX_assoc,
            extendComponentIso_hom_extendXIso_sndX_assoc]
          slice_rhs 2 4 =>
            rw [extendComponentIso_hom_extendXIso_sndX φ e j]
          have hsndE :
              (homotopyCofiber (HomologicalComplex.extendMap φ e)).d
                  (e.f i) (e.f j) ≫
                sndX (HomologicalComplex.extendMap φ e) (e.f j) =
              fstX (HomologicalComplex.extendMap φ e)
                    (e.f i) (e.f j) hij ≫
                  (HomologicalComplex.extendMap φ e).f (e.f j) +
                sndX (HomologicalComplex.extendMap φ e) (e.f i) ≫
                  (G.extend e).d (e.f i) (e.f j) := by
            exact d_sndX (HomologicalComplex.extendMap φ e)
              (e.f i) (e.f j) hij
          slice_rhs 1 2 => rw [hsndE]
          rw [HomologicalComplex.extendMap_f φ e rfl]
          rw [G.extend_d_eq e rfl rfl]
          simp [CategoryTheory.Preadditive.add_comp, Category.assoc]
      · exact ((homotopyCofiber φ).isZero_extend_X e j'
          (by simpa using hjmem)).eq_of_tgt _ _)

/--
Let C be preadditive with a zero object and binary biproducts. Let φ:F→G be a morphism of
c-complexes and e:c→c' an incoming-closed, relation-reflecting embedding. Write e_* for
extension by zero and H(φ) for the homotopy cofiber. Assume the relations of c and c' are
decidable. Assume every degree of c has an incoming edge. The forward morphism of
H(e_*φ)≅e_*H(φ) is exactly the universal comparison obtained from the extended target
inclusion and its null-homotopy.
-/
lemma extendIso_hom_eq_extendComparison :
    (extendIso φ e).hom = extendComparison φ e hc := by
  ext i'
  exact (extendComparison_f_eq φ e hc i').symm

/--
Let C be preadditive with a zero object and binary biproducts. Let φ:F→G be a morphism of
c-complexes and e:c→c' an incoming-closed, relation-reflecting embedding. Write e_* for
extension by zero and H(φ) for the homotopy cofiber. Assume the relations of c and c' are
decidable. The global target inclusion is preserved: inr_{e_*φ}≫extendIso(φ,e).hom =
e_*(inr_φ).
-/
@[reassoc]
lemma inr_extendIso_hom :
    inr (HomologicalComplex.extendMap φ e) ≫
        (extendIso φ e).hom =
      HomologicalComplex.extendMap (inr φ) e := by
  ext i'
  by_cases hmem : ∃ i, e.f i = i'
  · obtain ⟨i, rfl⟩ := hmem
    change inrX (HomologicalComplex.extendMap φ e) (e.f i) ≫
        (extendComponentIso φ e (e.f i)).hom =
      (HomologicalComplex.extendMap (inr φ) e).f (e.f i)
    rw [inrX_extendComponentIso_hom]
    rw [HomologicalComplex.extendMap_f (inr φ) e rfl]
    rfl
  · exact (G.isZero_extend_X e i' (by simpa using hmem)).eq_of_src _ _

/--
Let C be preadditive with a zero object and binary biproducts. Let φ:F→G be a morphism of
c-complexes and e:c→c' an incoming-closed, relation-reflecting embedding. Write e_* for
extension by zero and H(φ) for the homotopy cofiber. Assume the relations of c and c' are
decidable. For a reverse edge c.Rel j i, the first-summand inclusion at e(i)→e(j) followed by
the degree-e(j) forward component agrees with the original inclusion F_i→H(φ)_j through the
source and cofiber extension identifications.
-/
@[reassoc]
lemma inlX_extendIso_hom_f (i j : ι) (hji : c.Rel j i) :
    inlX (HomologicalComplex.extendMap φ e)
        (e.f i) (e.f j) (e.rel hji) ≫
        (extendIso φ e).hom.f (e.f j) =
      (F.extendXIso e rfl).hom ≫
        inlX φ i j hji ≫
        ((homotopyCofiber φ).extendXIso e rfl).inv :=
  inlX_extendComponentIso_hom φ e i j hji

end Object

variable [DecidableRel c.Rel] [DecidableRel c'.Rel]

section Naturality

variable (e : c.Embedding c') [e.IsTruncLE]
variable (hc : ∀ j : ι, ∃ i, c.Rel i j)
variable (hc' : ∀ j : ι', ∃ i, c'.Rel i j)

/--
Let C be preadditive with a zero object and binary biproducts, and e:c→c' incoming-closed and
relation-reflecting. Assume both relations are decidable and every degree in both shapes has a
predecessor. Let a be a commutative square between c-complex maps φ and ψ. The cofiber map of
the extended square followed by θ_ψ equals θ_φ followed by the extension of its cofiber map,
where θ_φ:H(e_*φ)≅e_*H(φ) is the canonical isomorphism.
-/
@[reassoc]
theorem extendIso_naturality
    {φ ψ : Arrow (HomologicalComplex C c)} (a : φ ⟶ ψ) :
    mapArrowHom
        (HomologicalComplex.extendMap φ.hom e)
        (HomologicalComplex.extendMap ψ.hom e) hc'
        ((e.extendFunctor C).mapArrow.map a) ≫
        (extendIso ψ.hom e).hom =
      (extendIso φ.hom e).hom ≫
        HomologicalComplex.extendMap
          (mapArrowHom φ.hom ψ.hom hc
            (Arrow.homMk' a.left a.right (w := a.w))) e := by
  let a' : Arrow.mk φ.hom ⟶ Arrow.mk ψ.hom :=
    Arrow.homMk' a.left a.right (w := a.w)
  let ae :
      Arrow.mk (HomologicalComplex.extendMap φ.hom e) ⟶
        Arrow.mk (HomologicalComplex.extendMap ψ.hom e) :=
    Arrow.homMk'
      (HomologicalComplex.extendMap a.left e)
      (HomologicalComplex.extendMap a.right e)
      (w := by
        rw [← HomologicalComplex.extendMap_comp,
          ← HomologicalComplex.extendMap_comp]
        exact congrArg (fun k ↦ HomologicalComplex.extendMap k e) a.w)
  change mapArrowHom
      (HomologicalComplex.extendMap φ.hom e)
      (HomologicalComplex.extendMap ψ.hom e) hc' ae ≫
      (extendIso ψ.hom e).hom =
    (extendIso φ.hom e).hom ≫
      HomologicalComplex.extendMap
        (mapArrowHom φ.hom ψ.hom hc a') e
  rw [extendIso_hom_eq_extendComparison
      (φ := ψ.hom) (e := e) (hc := hc),
    extendIso_hom_eq_extendComparison
      (φ := φ.hom) (e := e) (hc := hc)]
  apply mapArrowHom_desc_naturality_of_rel
  · have h := inr_mapArrowHom hc a'
    have h' := congrArg (fun k ↦ HomologicalComplex.extendMap k e) h
    rw [HomologicalComplex.extendMap_comp,
      HomologicalComplex.extendMap_comp] at h'
    exact h'.symm
  · intro i' j' hji
    by_cases hi' : ∃ i, e.f i = i'
    · obtain ⟨i, rfl⟩ := hi'
      obtain ⟨j, hj⟩ := e.mem_prev hji
      subst j'
      have hji' := (e.rel_iff j i).mp hji
      change
        (HomologicalComplex.extendMap a.left e).f (e.f i) ≫
            (extendInrCompHomotopy ψ.hom e hc).hom (e.f i) (e.f j) =
          (extendInrCompHomotopy φ.hom e hc).hom (e.f i) (e.f j) ≫
            (HomologicalComplex.extendMap
              (mapArrowHom φ.hom ψ.hom hc a') e).f (e.f j)
      rw [HomologicalComplex.extendMap_f a.left e rfl]
      rw [extendInrCompHomotopy_hom ψ.hom e hc i j hji',
        extendInrCompHomotopy_hom φ.hom e hc i j hji']
      rw [HomologicalComplex.extendMap_f
        (mapArrowHom φ.hom ψ.hom hc a') e rfl]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      have h := (inlX_mapArrowHom hc a' i j hji').symm
      change a.left.f i ≫ inlX ψ.hom i j hji' =
        inlX φ.hom i j hji' ≫
          (mapArrowHom φ.hom ψ.hom hc a').f j at h
      simpa only [Category.assoc] using congrArg
        (fun k ↦ (φ.left.extendXIso e rfl).hom ≫ k ≫
          ((homotopyCofiber ψ.hom).extendXIso e rfl).inv) h
    · exact (φ.left.isZero_extend_X e i' (by simpa using hi')).eq_of_src _ _

/--
Let C be preadditive with a zero object and binary biproducts, and e:c→c' incoming-closed and
relation-reflecting. Assume both relations are decidable and every degree in both shapes has a
predecessor. Let a be a commutative square between c-complex maps φ and ψ. The extended
cofiber map is θ_φ.inv≫H(e_*a)≫θ_ψ.hom. Thus the two cofiber maps are related by conjugation
through the extension isomorphisms.
-/
theorem extendMap_mapArrowHom
    {φ ψ : Arrow (HomologicalComplex C c)} (a : φ ⟶ ψ) :
    HomologicalComplex.extendMap
        (mapArrowHom φ.hom ψ.hom hc
          (Arrow.homMk' a.left a.right (w := a.w))) e =
      (extendIso φ.hom e).inv ≫
        mapArrowHom
          (HomologicalComplex.extendMap φ.hom e)
          (HomologicalComplex.extendMap ψ.hom e) hc'
          ((e.extendFunctor C).mapArrow.map a) ≫
        (extendIso ψ.hom e).hom := by
  apply (cancel_epi (extendIso φ.hom e).hom).1
  simp only [Iso.hom_inv_id_assoc]
  exact (extendIso_naturality e hc hc' a).symm

/--
Let C be preadditive with zero object and binary biproducts. Let e:c→c' be incoming-closed and
relation-reflecting, with decidable relations and a predecessor at every degree of each shape.
On the arrow categories of complexes, extension followed by homotopy cofiber is naturally
isomorphic to homotopy cofiber followed by extension.
-/
noncomputable def extendNatIso :
    (e.extendFunctor C).mapArrow ⋙ homotopyCofiberFunctor hc' ≅
      homotopyCofiberFunctor hc ⋙ e.extendFunctor C :=
  NatIso.ofComponents
    (fun φ ↦ extendIso φ.hom e)
    (fun a ↦ extendIso_naturality e hc hc' a)

/--
Let C be preadditive with a zero object and binary biproducts, and let e:c→c' be
incoming-closed and relation-reflecting. Assume both relations are decidable and every degree
of both shapes has a predecessor. For an arrow φ of c-complexes, the forward component of the
natural cofiber–extension isomorphism is θ_φ.hom:H(e_*φ)→e_*H(φ), where θ_φ is the canonical
extension comparison.
-/
@[simp]
lemma extendNatIso_hom_app (φ : Arrow (HomologicalComplex C c)) :
    (extendNatIso e hc hc').hom.app φ = (extendIso φ.hom e).hom :=
  rfl

/--
Let C be preadditive with a zero object and binary biproducts, and let e:c→c' be
incoming-closed and relation-reflecting. Assume both relations are decidable and every degree
of both shapes has a predecessor. For an arrow φ of c-complexes, the inverse component of the
natural cofiber–extension isomorphism is θ_φ.inv:e_*H(φ)→H(e_*φ).
-/
@[simp]
lemma extendNatIso_inv_app (φ : Arrow (HomologicalComplex C c)) :
    (extendNatIso e hc hc').inv.app φ = (extendIso φ.hom e).inv :=
  rfl

/--
Let C be preadditive with zero object and binary biproducts, let e:c→c' be incoming-closed and
relation-reflecting, and assume both relations are decidable. Let S=(A→B→D) be a short complex
of c-complexes. For θ:H(e_*S.f)≅e_*H(S.f), the canonical descent maps to the third term
satisfy θ.hom≫e_*(desc_S)=desc_{e_*S}.
-/
@[reassoc]
theorem extendIso_hom_descShortComplex
    (S : ShortComplex (HomologicalComplex C c)) :
    (extendIso S.f e).hom ≫
        HomologicalComplex.extendMap (descShortComplex S) e =
      descShortComplex (S.map (e.extendFunctor C)) := by
  let hMap : _root_.Homotopy
      (HomologicalComplex.extendMap S.f e ≫
        HomologicalComplex.extendMap S.g e) 0 :=
    _root_.Homotopy.ofEq (by
      rw [← HomologicalComplex.extendMap_comp, S.zero]
      exact HomologicalComplex.extendMap_zero _ _ e)
  let hOrig : _root_.Homotopy (S.f ≫ S.g) 0 :=
    _root_.Homotopy.ofEq S.zero
  change (extendIso S.f e).hom ≫
      HomologicalComplex.extendMap (desc S.f S.g hOrig) e =
    desc (HomologicalComplex.extendMap S.f e)
      (HomologicalComplex.extendMap S.g e) hMap
  have hInr :
      inr (HomologicalComplex.extendMap S.f e) ≫
          ((extendIso S.f e).hom ≫
            HomologicalComplex.extendMap (desc S.f S.g hOrig) e) =
        inr (HomologicalComplex.extendMap S.f e) ≫
          desc (HomologicalComplex.extendMap S.f e)
            (HomologicalComplex.extendMap S.g e) hMap := by
    rw [← Category.assoc]
    rw [inr_extendIso_hom]
    rw [← HomologicalComplex.extendMap_comp]
    simp only [inr_desc]
  ext i'
  simp only [HomologicalComplex.comp_f]
  by_cases hmem : ∃ i, e.f i = i'
  · obtain ⟨i, rfl⟩ := hmem
    by_cases hi : c.Rel i (c.next i)
    · apply ext_from_X (HomologicalComplex.extendMap S.f e)
        (e.f (c.next i)) (e.f i) (e.rel hi)
      · rw [inlX_extendIso_hom_f_assoc S.f e (c.next i) i hi]
        rw [HomologicalComplex.extendMap_f (desc S.f S.g hOrig) e rfl]
        simp only [Iso.inv_hom_id_assoc]
        rw [inlX_desc_f_assoc
          (φ := S.f) (α := S.g) (hα := hOrig)
          (c.next i) i hi]
        rw [inlX_desc_f
          (φ := HomologicalComplex.extendMap S.f e)
          (α := HomologicalComplex.extendMap S.g e)
          (hα := hMap) (e.f (c.next i)) (e.f i) (e.rel hi)]
        simp [hMap, hOrig]
      · simpa only [HomologicalComplex.comp_f, inr_f] using
          congrArg (fun k ↦ k.f (e.f i)) hInr
    · by_cases hi' : c'.Rel (e.f i) (c'.next (e.f i))
      · apply ext_from_X (HomologicalComplex.extendMap S.f e)
          (c'.next (e.f i)) (e.f i) hi'
        · exact (S.X₁.isZero_extend_X e _
            (not_mem_next_of_not_rel_next e i hi hi')).eq_of_src _ _
        · simpa only [HomologicalComplex.comp_f, inr_f] using
            congrArg (fun k ↦ k.f (e.f i)) hInr
      · apply ext_from_X' (HomologicalComplex.extendMap S.f e) (e.f i) hi'
        simpa only [HomologicalComplex.comp_f, inr_f] using
          congrArg (fun k ↦ k.f (e.f i)) hInr
  · have hG : IsZero ((S.X₂.extend e).X i') :=
      S.X₂.isZero_extend_X e i' (by simpa using hmem)
    have hF : ∀ j', c'.Rel i' j' → IsZero ((S.X₁.extend e).X j') := by
      intro j' hij
      exact S.X₁.isZero_extend_X e j'
        (not_mem_of_rel_of_not_mem_source e hij (by simpa using hmem))
    exact (isZero_X (HomologicalComplex.extendMap S.f e) i' hG hF).eq_of_src _ _

/--
Let C be preadditive with zero object and binary biproducts, let e:c→c' be incoming-closed and
relation-reflecting, and assume both relations are decidable. Let S=(A→B→D) be a short complex
of c-complexes. The extended descent map e_*(desc_S):e_*H(S.f)→e_*D equals θ.inv≫desc_{e_*S},
using θ:H(e_*S.f)≅e_*H(S.f).
-/
theorem extendMap_descShortComplex
    (S : ShortComplex (HomologicalComplex C c)) :
    HomologicalComplex.extendMap (descShortComplex S) e =
      (extendIso S.f e).inv ≫
        descShortComplex (S.map (e.extendFunctor C)) := by
  apply (cancel_epi (extendIso S.f e).hom).1
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using
    extendIso_hom_descShortComplex e S

end Naturality

end HomologicalComplex.homotopyCofiber
