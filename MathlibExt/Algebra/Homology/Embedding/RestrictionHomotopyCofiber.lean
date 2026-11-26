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
# Homotopy cofibers and restriction

For an outgoing-closed embedding of complex shapes, restricting a homotopy
cofiber is canonically isomorphic to taking the cofiber of the restricted
map. Both the shifted source coordinate and target coordinate are retained,
and source/target inclusions are compatible with the comparison.

When every degree has a predecessor in both shapes, the comparison is a
natural isomorphism of homotopy-cofiber functors on arrows. It also preserves
the canonical descent map from a short complex's cofiber to its third term.
-/

@[expose] public section
universe u v

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace HomologicalComplex.HasHomotopyCofiber

/--
Let C be a preadditive category, φ:F→G a map of c'-complexes, and e:c→c' a shape embedding
preserving and reflecting differential relations. If φ has the degreewise biproduct data
required for its homotopy cofiber, the restricted map F.restriction e→G.restriction e has that
data too.
-/
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

/--
Let K be a c'-complex in a preadditive category C and e:c→c' a relation-reflecting embedding.
At i, the canonical identification (K.restriction e)_i≅K_{e(i)} using the equality e(i)=e(i)
is the identity isomorphism.
-/
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

/--
Let e:c→c' be a relation-reflecting shape embedding whose image is closed under outgoing
differentials. If i has no outgoing edge in c, then e(i) has no outgoing edge in c': ¬c.Rel
i(next i) implies ¬c'.Rel e(i)(next e(i)).
-/
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

/--
Let C be preadditive with binary biproducts, let φ:F→G be a c'-complex map, and let e:c→c'
preserve and reflect relations with image closed under outgoing differentials (IsTruncGE).
Assume both relations are decidable, and write H(φ) for the homotopy cofiber. At each i there
is a canonical isomorphism (H(φ).restriction e)_i≅H(restrictionMap φ e)_i. Outgoing closure
identifies the shifted source coordinate F_{e(next i)} and the target coordinate G_{e(i)} on
both sides, including the no-successor case.
-/
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

/--
Let C be preadditive with binary biproducts, let φ:F→G be a c'-complex map, and let e:c→c'
preserve and reflect relations with image closed under outgoing differentials (IsTruncGE).
Assume both relations are decidable, and write H(φ) for the homotopy cofiber. For c.Rel i j,
the component comparison followed by the restricted cofiber's projection to (F.restriction
e)_j equals the ambient cofiber projection to F_{e(j)}, through the canonical restriction
coordinate isomorphisms.
-/
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

/--
Let C be preadditive with binary biproducts, let φ:F→G be a c'-complex map, and let e:c→c'
preserve and reflect relations with image closed under outgoing differentials (IsTruncGE).
Assume both relations are decidable, and write H(φ) for the homotopy cofiber. At i, the
component comparison followed by the projection to (G.restriction e)_i equals the ambient
cofiber's target projection at e(i), transported by the cofiber and G restriction
identifications.
-/
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

/--
Let C be preadditive with binary biproducts, let φ:F→G be a c'-complex map, and let e:c→c'
preserve and reflect relations with image closed under outgoing differentials (IsTruncGE).
Assume both relations are decidable, and write H(φ) for the homotopy cofiber. The component
comparisons assemble into an isomorphism H(φ).restriction e≅H(restrictionMap φ e), preserving
both cofiber coordinates at every retained degree.
-/
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

/--
Let C be preadditive with binary biproducts, let φ:F→G be a c'-complex map, and let e:c→c'
preserve and reflect relations with image closed under outgoing differentials (IsTruncGE).
Assume both relations are decidable, and write H(φ) for the homotopy cofiber. For c.Rel j i,
the ambient source inclusion F_{e(i)}→H(φ)_{e(j)}, followed by restriction identification and
the degree-j comparison, equals the inverse F restriction identification followed by the
restricted source inclusion.
-/
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

/--
Let C be preadditive with binary biproducts, let φ:F→G be a c'-complex map, and let e:c→c'
preserve and reflect relations with image closed under outgoing differentials (IsTruncGE).
Assume both relations are decidable, and write H(φ) for the homotopy cofiber. At i, the
ambient target inclusion G_{e(i)}→H(φ)_{e(i)}, followed by restriction identification and the
comparison, equals the inverse G restriction identification followed by the target inclusion
into the restricted cofiber.
-/
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

/--
Let C be preadditive with binary biproducts and let e:c→c' be outgoing-closed and
relation-reflecting. Assume both relations are decidable and every degree of both shapes has a
predecessor, so their homotopy-cofiber functors on arrows are defined. For a commutative
square a:φ→ψ of c'-complex maps, restriction of H(a) followed by θ_ψ equals θ_φ followed by
the cofiber map of the restricted square, where θ_φ:H(φ)|e≅H(φ|e).
-/
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

/--
Let C be preadditive with binary biproducts and let e:c→c' be outgoing-closed and
relation-reflecting. Assume both relations are decidable and every degree of both shapes has a
predecessor, so their homotopy-cofiber functors on arrows are defined. The functor taking a
homotopy cofiber and then restricting along e is naturally isomorphic to restriction on arrows
followed by the homotopy-cofiber functor.
-/
noncomputable def restrictionNatIso :
    homotopyCofiberFunctor hc' ⋙ e.restrictionFunctor C ≅
      (e.restrictionFunctor C).mapArrow ⋙ homotopyCofiberFunctor hc :=
  NatIso.ofComponents
    (fun φ ↦ restrictionIso φ.hom e)
    (fun a ↦ restrictionIso_naturality e hc hc' a)

/--
Let C be preadditive with binary biproducts and let e:c→c' be outgoing-closed and
relation-reflecting. Assume both relations are decidable and every degree of both shapes has a
predecessor, so their homotopy-cofiber functors on arrows are defined. At an arrow φ, the
forward component of that natural isomorphism is θ_φ.hom:H(φ)|e→H(φ|e), the canonical
restriction comparison.
-/
@[simp]
lemma restrictionNatIso_hom_app (φ : Arrow (HomologicalComplex C c')) :
    (restrictionNatIso e hc hc').hom.app φ = (restrictionIso φ.hom e).hom :=
  rfl

/--
Let C be preadditive with binary biproducts and let e:c→c' be outgoing-closed and
relation-reflecting. Assume both relations are decidable and every degree of both shapes has a
predecessor, so their homotopy-cofiber functors on arrows are defined. At an arrow φ, its
inverse component is θ_φ.inv:H(φ|e)→H(φ)|e.
-/
@[simp]
lemma restrictionNatIso_inv_app (φ : Arrow (HomologicalComplex C c')) :
    (restrictionNatIso e hc hc').inv.app φ = (restrictionIso φ.hom e).inv :=
  rfl

/--
Let C be preadditive with binary biproducts, e:c→c' outgoing-closed and relation-reflecting,
and both relations decidable. For a short complex S=(A→B→D) of c'-complexes, the canonical
cofiber comparison θ:H(S.f)|e≅H((S|e).f) satisfies θ.hom≫desc_{S|e}=restriction(desc_S).
-/
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
