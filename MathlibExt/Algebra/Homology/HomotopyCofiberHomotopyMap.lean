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
# Homotopy squares and maps of homotopy cofibers

Let C be preadditive with binary biproducts, and let c have decidable
differential relation and a predecessor in every degree. For complex maps
φ:F → G and ψ:F′ → G′, maps a:F → F′ and b:G → G′, and a homotopy
H:b∘φ ∼ ψ∘a, there is an induced map M:Cofib(φ) → Cofib(ψ).
In degree j with c.Rel(j,i), its biproduct coordinates are
(x,y) ↦ (aᵢ(x),Hᵢⱼ(x)+bⱼ(y)).
The homotopy occurs with a positive sign. A commuting square with its
zero-component homotopy gives the ordinary arrow-induced cofiber map.

If C has a zero object, the target inclusion and projection to Cofib(F → 0)
form the sequence G → Cofib(φ) → Cofib(F → 0), split in every degree.
The homotopy square induces a map of these sequences with components
b, M and the zero-target cofiber map induced by a.

For an abelian category the target sequence is short exact.
For nonnegative chain complexes, if a and b are quasi-isomorphisms then
M is a quasi-isomorphism. The constructions use an arbitrary shape; its index universe is
  independent
of the category object and morphism universes.
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

/-- Let C be preadditive with binary biproducts, and let c be a complex shape
with decidable differential relation and a predecessor in every degree.
For maps φ:F → G and ψ:F′ → G′, take a:F → F′, b:G → G′
and a homotopy H:b∘φ ∼ ψ∘a.

The nullhomotopy of the composite F → G → G′ → Cofib(ψ),
using b and the target cofiber inclusion, obtained by composing H with
that inclusion and the canonical nullhomotopy of ψ followed by its
cofiber inclusion. -/
def mapOfHomotopyNull :
    _root_.Homotopy (φ ≫ (b ≫ inr ψ)) 0 :=
  (_root_.Homotopy.ofEq ((Category.assoc φ b (inr ψ)).symm)).trans
    ((H.compRight (inr ψ)).trans
      ((_root_.Homotopy.ofEq (Category.assoc a ψ (inr ψ))).trans
        (((inrCompHomotopy ψ hc).compLeft a).trans
          (_root_.Homotopy.ofEq (comp_zero : a ≫ 0 = 0)))))

/-- Let C be preadditive with binary biproducts, and let c be a complex shape
with decidable differential relation and a predecessor in every degree.
For maps φ:F → G and ψ:F′ → G′, take a:F → F′, b:G → G′
and a homotopy H:b∘φ ∼ ψ∘a.

The induced cofiber map M:Cofib(φ) → Cofib(ψ), obtained from b
on the target and the nullhomotopy of inr_ψ∘b∘φ.
For c.Rel(j,i), its degree-j coordinates are
(x,y)↦(aᵢ(x),Hᵢⱼ(x)+bⱼ(y)). -/
def mapOfHomotopy : homotopyCofiber φ ⟶ homotopyCofiber ψ :=
  desc φ (b ≫ inr ψ) (mapOfHomotopyNull φ ψ hc a b H)

/-- Let C be preadditive with binary biproducts, and let c be a complex shape
with decidable differential relation and a predecessor in every degree.
For maps φ:F → G and ψ:F′ → G′, take a:F → F′, b:G → G′
and a homotopy H:b∘φ ∼ ψ∘a.

For the induced cofiber map M, the target inclusions commute with b:
M ∘ inr_φ = inr_ψ ∘ b as maps G → Cofib(ψ). -/
@[reassoc]
theorem inr_mapOfHomotopy :
    inr φ ≫ mapOfHomotopy φ ψ hc a b H = b ≫ inr ψ :=
  inr_desc φ (b ≫ inr ψ) (mapOfHomotopyNull φ ψ hc a b H)

/-- Let C be preadditive with binary biproducts, and let c be a complex shape
with decidable differential relation and a predecessor in every degree.
For maps φ:F → G and ψ:F′ → G′, take a:F → F′, b:G → G′
and a homotopy H:b∘φ ∼ ψ∘a.

For c.Rel(j,i), the shifted-source component of the induced map M is
Mⱼ ∘ inl_φ(i,j)
= inr_ψ(j) ∘ Hᵢⱼ + inl_ψ(i,j) ∘ aᵢ.
Thus the homotopy component is the positive off-diagonal term. -/
@[reassoc]
theorem inlX_mapOfHomotopy (i j : ι) (hji : c.Rel j i) :
    inlX φ i j hji ≫ (mapOfHomotopy φ ψ hc a b H).f j =
      H.hom i j ≫ inrX ψ j + a.f i ≫ inlX ψ i j hji := by
  rw [mapOfHomotopy, inlX_desc_f]
  simp only [mapOfHomotopyNull, _root_.Homotopy.trans_hom,
    _root_.Homotopy.ofEq_hom, _root_.Homotopy.compRight_hom,
    _root_.Homotopy.compLeft_hom, Pi.zero_apply, zero_add, add_zero,
    inrCompHomotopy_hom ψ hc i j hji, inr_f]

/-- Let C be preadditive with binary biproducts, and let c be a complex shape
with decidable differential relation and a predecessor in every degree.
For maps φ:F → G and ψ:F′ → G′, take a:F → F′, b:G → G′
and a homotopy H:b∘φ ∼ ψ∘a.

In every degree j the target component of the induced map M satisfies
Mⱼ ∘ inr_φ(j) = inr_ψ(j) ∘ bⱼ. -/
@[reassoc]
theorem inrX_mapOfHomotopy (j : ι) :
    inrX φ j ≫ (mapOfHomotopy φ ψ hc a b H).f j =
      b.f j ≫ inrX ψ j := by
  simpa only [HomologicalComplex.comp_f, inr_f] using
    congrArg (fun f => f.f j) (inr_mapOfHomotopy φ ψ hc a b H)

/-- Let C be preadditive with binary biproducts and let c have decidable
differential relation and a predecessor in every degree.
For φ:F → G, ψ:F′ → G′ and maps a:F → F′, b:G → G′ satisfying
b∘φ=ψ∘a, the cofiber map formed with the equality's zero-component
homotopy equals the map induced by this commuting arrow square. -/
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

/-- In a preadditive category C with a zero object and binary biproducts,
for a complex F of shape c with decidable differential relation, the
zero-target cofiber Cofib(0:F → 0). -/
abbrev zeroTarget (F : HomologicalComplex C c) :=
  homotopyCofiber (0 : F ⟶ (HomologicalComplex.zero : HomologicalComplex C c))

/-- Let C be preadditive with a zero object and binary biproducts, and let
c have decidable differential relation. For a complex map φ:F → G,
the commuting square from φ to the zero-target map F → 0 whose
source side is 1_F and whose target side is G → 0. -/
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

/-- Let C be preadditive with a zero object and binary biproducts, c have
decidable differential relation and a predecessor in every degree,
and φ:F → G be a complex map. The short complex
G —inr_φ→ Cofib(φ) —p_φ→ Cofib(F → 0),
where p_φ is induced by the square (1_F,G → 0); its composite is zero. -/
abbrev targetShortComplex : ShortComplex (HomologicalComplex C c) :=
  ShortComplex.mk (inr φ) (targetProjection φ hc) (by
    have h := inr_mapArrowHom hc (targetProjectionArrow φ)
    change inr φ ≫ targetProjection φ hc =
      (0 : G ⟶ (HomologicalComplex.zero : HomologicalComplex C c)) ≫
        inr (0 : F ⟶ (HomologicalComplex.zero : HomologicalComplex C c)) at h
    exact h.trans (by simp only [zero_comp]))

/-- Let C be preadditive with a zero object and binary biproducts, c have
decidable differential relation, and φ:F → G be a complex map.
For each degree j, the map Cofib(F → 0)ⱼ → Cofib(φ)ⱼ that includes
the shifted-source coordinate. If j has no outgoing shape relation,
it is zero. -/
def targetSection (j : ι) : (zeroTarget F).X j ⟶ (homotopyCofiber φ).X j :=
  if hj : c.Rel j (c.next j) then
    fstX (0 : F ⟶ (HomologicalComplex.zero : HomologicalComplex C c)) j (c.next j) hj ≫
      inlX φ (c.next j) j hj
  else 0

/-- Let C be preadditive with a zero object and binary biproducts, c have
decidable differential relation and a predecessor in every degree,
and φ:F → G be a complex map. The sequence
Gⱼ → Cofib(φ)ⱼ → Cofib(F → 0)ⱼ has a splitting in each degree j:
the retraction onto Gⱼ is the target-coordinate projection and the
section from the zero-target cofiber includes the shifted-source coordinate. -/
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

/-- Let C be preadditive with a zero object and binary biproducts and let
c have decidable differential relation and a predecessor in every
degree. For a complex map a:F → F′, the induced map
Cofib(F → 0) → Cofib(F′ → 0), given by the arrow square with source
map a and the unique map of zero targets. -/
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

/-- Let C be preadditive with binary biproducts, and let c be a complex shape
with decidable differential relation and a predecessor in every degree.
For maps φ:F → G and ψ:F′ → G′, take a:F → F′, b:G → G′
and a homotopy H:b∘φ ∼ ψ∘a.

Assume also that C has a zero object. The induced morphism between
G → Cofib(φ) → Cofib(F → 0) and
G′ → Cofib(ψ) → Cofib(F′ → 0) has first component b,
middle component M(a,b,H), and third component the zero-target
cofiber map induced by a. -/
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

/-- Let C be abelian and c a complex shape with decidable differential
relation and a predecessor in every degree. For a complex map
φ:F → G, the sequence
0 → G → Cofib(φ) → Cofib(F → 0) → 0
with its target inclusion and zero-target projection is short exact. -/
theorem targetShortComplex_shortExact :
    (targetShortComplex φ hc).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    (fun j => (targetShortComplexSplitting φ hc j).shortExact)

section DownNat

variable {F G F' G' : ChainComplex C ℕ}

/-- In an abelian category C, if a:F → F′ is a quasi-isomorphism of
nonnegative chain complexes, the induced zero-target cofiber map
Cofib(F → 0) → Cofib(F′ → 0), using the predecessors n+1,
is a quasi-isomorphism. -/
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

/-- Let C be abelian, φ:F → G and ψ:F′ → G′ maps of nonnegative
chain complexes, and a:F → F′, b:G → G′ quasi-isomorphisms.
For any homotopy H:b∘φ ∼ ψ∘a, the induced map
M(a,b,H):Cofib(φ) → Cofib(ψ), using predecessors n+1,
is a quasi-isomorphism. -/
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
