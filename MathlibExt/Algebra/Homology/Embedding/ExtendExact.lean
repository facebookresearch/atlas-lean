/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Embedding.ExtendHomologyFunctor
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequence

/-!
# Short exact sequences under zero extension

Zero extension along an embedding of complex shapes preserves short exact
sequences. The extension homology comparisons commute with their
connecting morphisms.
-/

@[expose] public section

open CategoryTheory Category Limits

universe v u

namespace ShortComplex.ShortExact

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Extension along an arbitrary embedding of complex shapes preserves short exactness.

The proof is degreewise in the target shape via
`HomologicalComplex.shortExact_iff_degreewise_shortExact`.  For a degree outside
the image of the embedding every component of the extended complexes is zero.  For a
degree inside the image we transport along the canonical isomorphisms
`HomologicalComplex.extendXIso` and use `HomologicalComplex.extendMap_f` to check
that the degreewise short complexes are isomorphic. -/
theorem map_extendFunctor
    {ι : Type*} {ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
    (e : c.Embedding c') (S : ShortComplex (HomologicalComplex C c)) (hS : S.ShortExact) :
    (S.map (e.extendFunctor C)).ShortExact := by
  rw [HomologicalComplex.shortExact_iff_degreewise_shortExact]
  intro i'
  by_cases h_exists : ∃ i, e.f i = i'
  · obtain ⟨i, hi⟩ := h_exists
    have hS_i : (S.map (HomologicalComplex.eval C c i)).ShortExact :=
      (HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS i
    let F := e.extendFunctor C
    let Tz : ShortComplex C := (S.map F).map (HomologicalComplex.eval C c' i')
    let Ui : ShortComplex C := S.map (HomologicalComplex.eval C c i)
    let e₁ : Tz.X₁ ≅ Ui.X₁ :=
      HomologicalComplex.extendXIso (K := S.X₁) (e := e) hi
    let e₂ : Tz.X₂ ≅ Ui.X₂ :=
      HomologicalComplex.extendXIso (K := S.X₂) (e := e) hi
    let e₃ : Tz.X₃ ≅ Ui.X₃ :=
      HomologicalComplex.extendXIso (K := S.X₃) (e := e) hi
    have h₁₂ : e₁.hom ≫ Ui.f = Tz.f ≫ e₂.hom := by
      have hTz : Tz.f = (HomologicalComplex.extendMap S.f e).f i' := rfl
      have hUi : Ui.f = S.f.f i := rfl
      rw [hTz, hUi]
      have hmap := HomologicalComplex.extendMap_f (φ := S.f) (e := e) hi
      change (HomologicalComplex.extendXIso S.X₁ e hi).hom ≫ S.f.f i =
          (HomologicalComplex.extendMap S.f e).f i' ≫
            (HomologicalComplex.extendXIso S.X₂ e hi).hom
      rw [hmap]
      simp
    have h₂₃ : e₂.hom ≫ Ui.g = Tz.g ≫ e₃.hom := by
      have hTz : Tz.g = (HomologicalComplex.extendMap S.g e).f i' := rfl
      have hUi : Ui.g = S.g.f i := rfl
      rw [hTz, hUi]
      have hmap := HomologicalComplex.extendMap_f (φ := S.g) (e := e) hi
      change (HomologicalComplex.extendXIso S.X₂ e hi).hom ≫ S.g.f i =
          (HomologicalComplex.extendMap S.g e).f i' ≫
            (HomologicalComplex.extendXIso S.X₃ e hi).hom
      rw [hmap]
      simp
    let iso : Tz ≅ Ui := ShortComplex.isoMk e₁ e₂ e₃ h₁₂ h₂₃
    exact ShortComplex.shortExact_of_iso iso.symm hS_i
  · have hmem : ∀ i, e.f i ≠ i' := fun i hi => h_exists ⟨i, hi⟩
    have hX₁ : IsZero ((S.X₁.extend e).X i') :=
      HomologicalComplex.isZero_extend_X _ _ _ hmem
    have hX₂ : IsZero ((S.X₂.extend e).X i') :=
      HomologicalComplex.isZero_extend_X _ _ _ hmem
    have hX₃ : IsZero ((S.X₃.extend e).X i') :=
      HomologicalComplex.isZero_extend_X _ _ _ hmem
    let Tz : ShortComplex C :=
      (S.map (e.extendFunctor C)).map (HomologicalComplex.eval C c' i')
    have hX₁' : IsZero Tz.X₁ := hX₁
    have hX₂' : IsZero Tz.X₂ := hX₂
    have hX₃' : IsZero Tz.X₃ := hX₃
    exact ShortComplex.ShortExact.mk' (Tz.exact_of_isZero_X₂ hX₂') (hX₁'.mono Tz.f) (hX₃'.epi Tz.g)

/-- Connecting morphisms commute with zero-extension along a shape embedding.

For `S` short exact over `c`, the extended connecting morphism at `i', j'`
agrees with the original at `i, j` conjugated by the canonical
`extendHomologyIso`s. Every relation proof and direction is explicit. -/
theorem map_extendFunctor_δ
    {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
    (e : c.Embedding c') (S : ShortComplex (HomologicalComplex C c))
    (hS : S.ShortExact) (i j : ι) (i' j' : ι')
    (hi : e.f i = i') (hj : e.f j = j')
    (hij : c.Rel i j) (hij' : c'.Rel i' j')
    [S.X₁.HasHomology i] [S.X₂.HasHomology i] [S.X₃.HasHomology i]
    [S.X₁.HasHomology j] [S.X₂.HasHomology j] [S.X₃.HasHomology j] :
    (S.X₃.extendHomologyIso e hi).hom ≫ hS.δ i j hij =
      (map_extendFunctor e S hS).δ i' j' hij' ≫
        (S.X₁.extendHomologyIso e hj).hom := by
  let F := e.extendFunctor C
  let S' := S.map F
  let hSF : S'.ShortExact := map_extendFunctor e S hS
  let src := HomologicalComplex.HomologySequence.snakeInput hS i j hij
  let tgt := HomologicalComplex.HomologySequence.snakeInput hSF i' j' hij'
  let eH_i : F ⋙ HomologicalComplex.homologyFunctor C c' i' ⟶
      HomologicalComplex.homologyFunctor C c i :=
    (HomologicalComplex.extendHomologyFunctorIso e i i' hi).hom
  let eH_j : F ⋙ HomologicalComplex.homologyFunctor C c' j' ⟶
      HomologicalComplex.homologyFunctor C c j :=
    (HomologicalComplex.extendHomologyFunctorIso e j j' hj).hom
  let eO_i : F ⋙ HomologicalComplex.opcyclesFunctor C c' i' ⟶
      HomologicalComplex.opcyclesFunctor C c i :=
    (HomologicalComplex.extendOpcyclesFunctorIso e i i' hi).hom
  let eC_j : F ⋙ HomologicalComplex.cyclesFunctor C c' j' ⟶
      HomologicalComplex.cyclesFunctor C c j :=
    (HomologicalComplex.extendCyclesFunctorIso e j j' hj).hom
  have h_toCycles : ∀ (K : HomologicalComplex C c) [K.HasHomology j]
      [(K.extend e).HasHomology j'],
      (K.extendXIso e hi).hom ≫ K.toCycles i j =
        (K.extend e).toCycles i' j' ≫ (K.extendCyclesIso e hj).hom := by
    intro K hK hKe
    simp [← cancel_mono (K.iCycles j), HomologicalComplex.toCycles_i,
      HomologicalComplex.extendCyclesIso_hom_iCycles, K.extend_d_eq e hi hj]
  have h_opToCyc : ∀ (K : HomologicalComplex C c) [K.HasHomology i]
      [K.HasHomology j] [(K.extend e).HasHomology i'] [(K.extend e).HasHomology j'],
      (K.extendOpcyclesIso e hi).hom ≫ K.opcyclesToCycles i j =
        (K.extend e).opcyclesToCycles i' j' ≫ (K.extendCyclesIso e hj).hom := by
    intro K hKi hKj hKei hKej
    simp [← cancel_epi ((K.extend e).pOpcycles i'),
      HomologicalComplex.pOpcycles_opcyclesToCycles, h_toCycles K]
  let φ : tgt ⟶ src :=
    { f₀ := S.mapNatTrans eH_i
      f₁ := S.mapNatTrans eO_i
      f₂ := S.mapNatTrans eC_j
      f₃ := S.mapNatTrans eH_j
      comm₀₁ := by
        apply ShortComplex.hom_ext
        · change (S.X₁.extendHomologyIso e hi).hom ≫ S.X₁.homologyι i =
            (S.X₁.extend e).homologyι i' ≫ (S.X₁.extendOpcyclesIso e hi).hom
          exact HomologicalComplex.extendHomologyIso_hom_homologyι _ e hi
        · change (S.X₂.extendHomologyIso e hi).hom ≫ S.X₂.homologyι i =
            (S.X₂.extend e).homologyι i' ≫ (S.X₂.extendOpcyclesIso e hi).hom
          exact HomologicalComplex.extendHomologyIso_hom_homologyι _ e hi
        · change (S.X₃.extendHomologyIso e hi).hom ≫ S.X₃.homologyι i =
            (S.X₃.extend e).homologyι i' ≫ (S.X₃.extendOpcyclesIso e hi).hom
          exact HomologicalComplex.extendHomologyIso_hom_homologyι _ e hi
      comm₁₂ := by
        apply ShortComplex.hom_ext
        · change (S.X₁.extendOpcyclesIso e hi).hom ≫ S.X₁.opcyclesToCycles i j =
            (S.X₁.extend e).opcyclesToCycles i' j' ≫
              (S.X₁.extendCyclesIso e hj).hom
          exact h_opToCyc (S.X₁)
        · change (S.X₂.extendOpcyclesIso e hi).hom ≫ S.X₂.opcyclesToCycles i j =
            (S.X₂.extend e).opcyclesToCycles i' j' ≫
              (S.X₂.extendCyclesIso e hj).hom
          exact h_opToCyc (S.X₂)
        · change (S.X₃.extendOpcyclesIso e hi).hom ≫ S.X₃.opcyclesToCycles i j =
            (S.X₃.extend e).opcyclesToCycles i' j' ≫
              (S.X₃.extendCyclesIso e hj).hom
          exact h_opToCyc (S.X₃)
      comm₂₃ := by
        apply ShortComplex.hom_ext
        · change (S.X₁.extendCyclesIso e hj).hom ≫ S.X₁.homologyπ j =
            (S.X₁.extend e).homologyπ j' ≫ (S.X₁.extendHomologyIso e hj).hom
          exact (HomologicalComplex.homologyπ_extendHomologyIso_hom _ e hj).symm
        · change (S.X₂.extendCyclesIso e hj).hom ≫ S.X₂.homologyπ j =
            (S.X₂.extend e).homologyπ j' ≫ (S.X₂.extendHomologyIso e hj).hom
          exact (HomologicalComplex.homologyπ_extendHomologyIso_hom _ e hj).symm
        · change (S.X₃.extendCyclesIso e hj).hom ≫ S.X₃.homologyπ j =
            (S.X₃.extend e).homologyπ j' ≫ (S.X₃.extendHomologyIso e hj).hom
          exact (HomologicalComplex.homologyπ_extendHomologyIso_hom _ e hj).symm }
  have hn := ShortComplex.SnakeInput.naturality_δ φ
  dsimp [src, tgt] at hn ⊢
  exact hn.symm

end ShortComplex.ShortExact

end
