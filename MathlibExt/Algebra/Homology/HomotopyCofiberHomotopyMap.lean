/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.HomotopyCofiberDownNatQuasiIso
public import MathlibExt.Algebra.Homology.ShortComplex.MiddleQuasiIso
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-!
# Homotopy squares and the original homotopy cofiber

The native cofiber descendant constructs the map of a homotopy square.
Its component formulas retain the actual two vertical maps and homotopy.
For nonnegative chain complexes, the native cofiber of the zero-target
map supplies the quotient of the target inclusion. The ordinary binary
biproduct decomposition proves this short complex degreewise split.
The existing homology-sequence comparison then proves that a homotopy
square with quasi-isomorphisms on both vertical sides induces a
quasi-isomorphism on the same native cofibers.

This extends the native cochain mapping-cone API to general complex shapes
and nonnegative chain complexes. It introduces no alternative cone model.

-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive

universe u v w

namespace HomologicalComplex.homotopyCofiber

section Preadditive

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasBinaryBiproducts C]
  {ι : Type w} {c : ComplexShape ι} [DecidableRel c.Rel]
  {F G F' G' : HomologicalComplex C c}
  (φ : F ⟶ G) (ψ : F' ⟶ G')
  (hc : ∀ j : ι, ∃ i, c.Rel i j)
  (a : F ⟶ F') (b : G ⟶ G')
  (H : _root_.Homotopy (φ ≫ b) (a ≫ ψ))

/-- The actual nullhomotopy into the target cofiber of a homotopy square. -/
def mapOfHomotopyNull :
    _root_.Homotopy (φ ≫ (b ≫ inr ψ)) 0 :=
  (_root_.Homotopy.ofEq ((Category.assoc φ b (inr ψ)).symm)).trans
    ((H.compRight (inr ψ)).trans
      ((_root_.Homotopy.ofEq (Category.assoc a ψ (inr ψ))).trans
        (((inrCompHomotopy ψ hc).compLeft a).trans
          (_root_.Homotopy.ofEq (comp_zero : a ≫ 0 = 0)))))

/-- Map the native cofibers using the actual vertical maps and homotopy. -/
def mapOfHomotopy : homotopyCofiber φ ⟶ homotopyCofiber ψ :=
  desc φ (b ≫ inr ψ) (mapOfHomotopyNull φ ψ hc a b H)

/-- The actual right vertical map is retained strictly. -/
@[reassoc]
theorem inr_mapOfHomotopy :
    inr φ ≫ mapOfHomotopy φ ψ hc a b H = b ≫ inr ψ :=
  inr_desc φ (b ≫ inr ψ) (mapOfHomotopyNull φ ψ hc a b H)

/-- The homotopy is the only off-diagonal component of the native cone map. -/
@[reassoc]
theorem inlX_mapOfHomotopy (i j : ι) (hji : c.Rel j i) :
    inlX φ i j hji ≫ (mapOfHomotopy φ ψ hc a b H).f j =
      H.hom i j ≫ inrX ψ j + a.f i ≫ inlX ψ i j hji := by
  rw [mapOfHomotopy, inlX_desc_f]
  simp only [mapOfHomotopyNull, _root_.Homotopy.trans_hom,
    _root_.Homotopy.ofEq_hom, _root_.Homotopy.compRight_hom,
    _root_.Homotopy.compLeft_hom, Pi.zero_apply, zero_add, add_zero,
    inrCompHomotopy_hom ψ hc i j hji, inr_f]

/-- The original target component is retained in each native cone degree. -/
@[reassoc]
theorem inrX_mapOfHomotopy (j : ι) :
    inrX φ j ≫ (mapOfHomotopy φ ψ hc a b H).f j =
      b.f j ≫ inrX ψ j := by
  simpa only [HomologicalComplex.comp_f, inr_f] using
    congrArg (fun f => f.f j) (inr_mapOfHomotopy φ ψ hc a b H)

/-- A strict square recovers the existing native arrow-cofiber map. -/
theorem mapOfHomotopy_ofEq (h : φ ≫ b = a ≫ ψ) :
    mapOfHomotopy φ ψ hc a b (_root_.Homotopy.ofEq h) =
      mapArrowHom φ ψ hc (Arrow.homMk' a b h.symm) := by
  let s : Arrow.mk φ ⟶ Arrow.mk ψ := Arrow.homMk' a b h.symm
  change mapOfHomotopy φ ψ hc a b (_root_.Homotopy.ofEq h) = mapArrowHom φ ψ hc s
  ext j
  by_cases hj : c.Rel j (c.next j)
  · apply ext_from_X φ (c.next j) j hj
    · rw [inlX_mapOfHomotopy φ ψ hc a b (_root_.Homotopy.ofEq h) (c.next j) j hj,
        inlX_mapArrowHom hc s (c.next j) j hj]
      simp only [_root_.Homotopy.ofEq_hom, Pi.zero_apply, zero_comp, zero_add]
      rfl
    · rw [inrX_mapOfHomotopy φ ψ hc a b (_root_.Homotopy.ofEq h) j,
        inrX_mapArrowHom hc s j]
      rfl
  · apply ext_from_X' φ j hj
    rw [inrX_mapOfHomotopy φ ψ hc a b (_root_.Homotopy.ofEq h) j,
      inrX_mapArrowHom hc s j]
    rfl

section TargetSequence

variable [HasZeroObject C]

/-- Use the native zero-target cofiber, without a second suspension model. -/
abbrev zeroTarget (F : HomologicalComplex C c) :=
  homotopyCofiber (0 : F ⟶ (HomologicalComplex.zero : HomologicalComplex C c))

/-- The quotient map is the native cofiber map of the actual zero-target square. -/
def targetProjectionArrow :
    Arrow.mk φ ⟶ Arrow.mk (0 : F ⟶ (HomologicalComplex.zero : HomologicalComplex C c)) :=
  Arrow.homMk' (𝟙 F) (0 : G ⟶ (HomologicalComplex.zero : HomologicalComplex C c)) (by simp)

def targetProjection : homotopyCofiber φ ⟶ zeroTarget F :=
  mapArrowHom φ (0 : F ⟶ (HomologicalComplex.zero : HomologicalComplex C c)) hc
    (targetProjectionArrow φ)

@[reassoc]
theorem inrX_targetProjection (j : ι) :
    inrX φ j ≫ (targetProjection φ hc).f j = 0 := by
  have h := inrX_mapArrowHom hc (targetProjectionArrow φ) j
  change inrX φ j ≫ (targetProjection φ hc).f j =
    (0 : G ⟶ (HomologicalComplex.zero : HomologicalComplex C c)).f j ≫
      inrX (0 : F ⟶ (HomologicalComplex.zero : HomologicalComplex C c)) j at h
  exact h.trans (by simp only [HomologicalComplex.zero_f, zero_comp])

@[reassoc]
theorem inlX_targetProjection (i j : ι) (hji : c.Rel j i) :
    inlX φ i j hji ≫ (targetProjection φ hc).f j =
      inlX (0 : F ⟶ (HomologicalComplex.zero : HomologicalComplex C c)) i j hji := by
  have h := inlX_mapArrowHom hc (targetProjectionArrow φ) i j hji
  change inlX φ i j hji ≫ (targetProjection φ hc).f j =
    (𝟙 (F.X i)) ≫
      inlX (0 : F ⟶ (HomologicalComplex.zero : HomologicalComplex C c)) i j hji at h
  exact h.trans (by simp only [HomologicalComplex.id_f, Category.id_comp])

/-- The target inclusion and native zero-target quotient form a short complex. -/
abbrev targetShortComplex : ShortComplex (HomologicalComplex C c) :=
  ShortComplex.mk (inr φ) (targetProjection φ hc) (by
    have h := inr_mapArrowHom hc (targetProjectionArrow φ)
    change inr φ ≫ targetProjection φ hc =
      (0 : G ⟶ (HomologicalComplex.zero : HomologicalComplex C c)) ≫
        inr (0 : F ⟶ (HomologicalComplex.zero : HomologicalComplex C c)) at h
    exact h.trans (by simp only [zero_comp]))

/-- The quotient has a pointwise section; this is not asserted natural in degrees. -/
def targetSection (j : ι) : (zeroTarget F).X j ⟶ (homotopyCofiber φ).X j :=
  if hj : c.Rel j (c.next j) then
    fstX (0 : F ⟶ (HomologicalComplex.zero : HomologicalComplex C c)) j (c.next j) hj ≫
      inlX φ (c.next j) j hj
  else 0

/-- Native cofiber coordinates compute the pointwise splitting of the target sequence. -/
def targetShortComplexSplitting (j : ι) :
    ((targetShortComplex φ hc).map (HomologicalComplex.eval C c j)).Splitting where
  r := sndX φ j
  s := targetSection φ j
  f_r := inrX_sndX φ j
  s_g := by
    change targetSection φ j ≫ (targetProjection φ hc).f j = 𝟙 _
    by_cases hj : c.Rel j (c.next j)
    · apply ext_from_X
        (0 : F ⟶ (HomologicalComplex.zero : HomologicalComplex C c)) (c.next j) j hj
      · simp only [targetSection, dite_eq_left hj, Category.assoc, inlX_fstX_assoc,
          Category.id_comp, Category.comp_id, inlX_targetProjection]
        exact (Category.comp_id _).symm
      · have hZ : IsZero ((HomologicalComplex.zero : HomologicalComplex C c).X j) := by
          exact (HomologicalComplex.eval C c j).map_isZero HomologicalComplex.isZero_zero
        exact hZ.eq_of_src _ _
    · have hZ : IsZero ((HomologicalComplex.zero : HomologicalComplex C c).X j) := by
        exact (HomologicalComplex.eval C c j).map_isZero HomologicalComplex.isZero_zero
      exact (hZ.of_iso (XIso (0 : F ⟶
        (HomologicalComplex.zero : HomologicalComplex C c)) j hj)).eq_of_src _ _
  id := by
    let r : (homotopyCofiber φ).X j ⟶ G.X j := sndX φ j
    let i : G.X j ⟶ (homotopyCofiber φ).X j := inrX φ j
    change r ≫ i +
      (targetProjection φ hc).f j ≫ targetSection φ j = 𝟙 _
    by_cases hj : c.Rel j (c.next j)
    · apply ext_from_X φ (c.next j) j hj
      · simp only [r, i, comp_add, Category.assoc, inlX_sndX_assoc,
          zero_comp, zero_add, inlX_targetProjection_assoc, targetSection,
          dite_eq_left hj, inlX_fstX_assoc, Category.id_comp, Category.comp_id]
        exact (Category.comp_id _).symm
      · simp only [r, i, comp_add, Category.assoc, inrX_sndX_assoc,
          Category.id_comp, inrX_targetProjection_assoc, zero_comp, add_zero,
          Category.comp_id]
        exact (Category.comp_id _).symm
    · simp only [r, i, targetSection, dite_eq_right hj, comp_zero, add_zero, sndX_inrX φ j hj]
      rfl

/-- The source vertical map induces the existing native map of zero-target cofibers. -/
def zeroTargetMap (a : F ⟶ F') : zeroTarget F ⟶ zeroTarget F' :=
  mapArrowHom
    (0 : F ⟶ (HomologicalComplex.zero : HomologicalComplex C c))
    (0 : F' ⟶ (HomologicalComplex.zero : HomologicalComplex C c)) hc
    (Arrow.homMk' a (0 : (HomologicalComplex.zero : HomologicalComplex C c) ⟶
      HomologicalComplex.zero) (by simp))

@[reassoc]
theorem inlX_zeroTargetMap (a : F ⟶ F') (i j : ι) (hji : c.Rel j i) :
    inlX (0 : F ⟶ (HomologicalComplex.zero : HomologicalComplex C c)) i j hji ≫
        (zeroTargetMap hc a).f j =
      a.f i ≫
        inlX (0 : F' ⟶ (HomologicalComplex.zero : HomologicalComplex C c)) i j hji := by
  let s : Arrow.mk (0 : F ⟶ (HomologicalComplex.zero : HomologicalComplex C c)) ⟶
      Arrow.mk (0 : F' ⟶ (HomologicalComplex.zero : HomologicalComplex C c)) :=
    Arrow.homMk' a (0 : (HomologicalComplex.zero : HomologicalComplex C c) ⟶
      HomologicalComplex.zero) (by simp)
  exact inlX_mapArrowHom hc s i j hji

/-- The homotopy square induces the original strict map of target short complexes. -/
def targetShortComplexMap :
    targetShortComplex φ hc ⟶ targetShortComplex ψ hc where
  τ₁ := b
  τ₂ := mapOfHomotopy φ ψ hc a b H
  τ₃ := zeroTargetMap hc a
  comm₁₂ := (inr_mapOfHomotopy φ ψ hc a b H).symm
  comm₂₃ := by
    change mapOfHomotopy φ ψ hc a b H ≫ targetProjection ψ hc =
      targetProjection φ hc ≫ zeroTargetMap hc a
    ext j
    by_cases hj : c.Rel j (c.next j)
    · apply ext_from_X φ (c.next j) j hj
      · simp only [HomologicalComplex.comp_f, inlX_mapOfHomotopy_assoc,
          add_comp, Category.assoc, inrX_targetProjection, comp_zero,
          zero_add, inlX_targetProjection, inlX_targetProjection_assoc, inlX_zeroTargetMap]
      · simp only [HomologicalComplex.comp_f, inrX_mapOfHomotopy_assoc,
          Category.assoc, inrX_targetProjection, comp_zero,
          inrX_targetProjection_assoc, zero_comp]
    · apply ext_from_X' φ j hj
      simp only [HomologicalComplex.comp_f, inrX_mapOfHomotopy_assoc,
        Category.assoc, inrX_targetProjection, comp_zero,
        inrX_targetProjection_assoc, zero_comp]

end TargetSequence

end Preadditive

section Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]
  {ι : Type w} {c : ComplexShape ι} [DecidableRel c.Rel]
  {F G : HomologicalComplex C c} (φ : F ⟶ G)
  (hc : ∀ j : ι, ∃ i, c.Rel i j)

/-- The target sequence is short exact, earned from its computed binary biproduct coordinates. -/
theorem targetShortComplex_shortExact :
    (targetShortComplex φ hc).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    (fun j => (targetShortComplexSplitting φ hc j).shortExact)

section DownNat

variable {F G F' G' : ChainComplex C ℕ}

/-- Quasi-isomorphism of native zero-target cofibers follows from the original source map. -/
theorem quasiIso_zeroTargetMap_downNat (a : F ⟶ F') (ha : QuasiIso a) :
    QuasiIso (zeroTargetMap (fun j : ℕ => ⟨j + 1, by simp⟩) a) := by
  let Z : ChainComplex C ℕ := HomologicalComplex.zero
  let q : Arrow.mk (0 : F ⟶ Z) ⟶ Arrow.mk (0 : F' ⟶ Z) :=
    Arrow.homMk' a 0 (by simp)
  have hZ : IsZero Z := HomologicalComplex.isZero_zero
  have hRight : QuasiIso q.right := by
    change QuasiIso (0 : Z ⟶ Z)
    rw [hZ.eq_of_src (0 : Z ⟶ Z) (𝟙 Z)]
    infer_instance
  exact quasiIso_mapArrowHom_downNat q ha hRight

/-- An actual homotopy square of nonnegative chain maps preserves native cone quasi-isomorphisms. -/
theorem quasiIso_mapOfHomotopy_downNat
    {φ : F ⟶ G} {ψ : F' ⟶ G'} (a : F ⟶ F') (b : G ⟶ G')
    (H : _root_.Homotopy (φ ≫ b) (a ≫ ψ))
    (ha : QuasiIso a) (hb : QuasiIso b) :
    QuasiIso (mapOfHomotopy φ ψ (fun j : ℕ => ⟨j + 1, by simp⟩) a b H) := by
  let hc : ∀ j : ℕ, ∃ i, (ComplexShape.down ℕ).Rel i j :=
    fun j => ⟨j + 1, by simp⟩
  let s := targetShortComplexMap φ ψ hc a b H
  have hThird : QuasiIso s.τ₃ := quasiIso_zeroTargetMap_downNat a ha
  exact HomologicalComplex.HomologySequence.quasiIso_τ₂ s
    (targetShortComplex_shortExact φ hc) (targetShortComplex_shortExact ψ hc)
    hb hThird

end DownNat

end Abelian

end HomologicalComplex.homotopyCofiber

end
