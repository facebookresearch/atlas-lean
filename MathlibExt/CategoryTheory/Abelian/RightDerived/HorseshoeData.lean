/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
/-
Author: Muse Code
-/
module

public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.CommSq
public import MathlibExt.CategoryTheory.Abelian.Injective.Horseshoe

/-!
# Long exact sequences from compatible injective resolutions

`Functor.RightDerived.HorseshoeData` records three injective resolutions,
compatible lifts of a short exact sequence, and degreewise splittings. An
additive functor sends this diagram to a short exact sequence of complexes.
Its homology sequence transports to the right-derived functors using the
chosen resolution comparison isomorphisms.

The connecting morphism and five-arrow sequence are defined once for arbitrary
compatible data. `HorseshoeData.Hom` provides naturality for compatible resolution
maps. `HorseshoeData.ofEndpoints` embeds the existing injective horseshoe with
prescribed endpoint resolutions into this same interface. The Hartshorne facade
retains its own canonical middle-resolution factory and forwards to this API.
-/

@[expose] public section

namespace CategoryTheory

open Category Limits HomologicalComplex

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasInjectiveResolutions C]
variable {D : Type u₂} [Category.{v₂} D] [Abelian D]

namespace Functor.RightDerived

/-- Horseshoe-type input data for the long exact sequence of right-derived
functors: injective resolutions of the three terms of a short exact sequence
`S`, with chosen lifts of `S.f` and `S.g` to the resolution complexes, plus a
degreewise splitting of the resulting diagram of complexes.

The middle resolution and the splittings are arbitrary compatible choices.
`HorseshoeData.ofEndpoints` supplies such data from the injective horseshoe
with prescribed endpoint resolutions. Source-specific factories may supply
other compatible middle resolutions without changing this interface. -/
@[ext]
structure HorseshoeData (S : ShortComplex C) (hS : S.ShortExact) where
  /-- Chosen injective resolution of the left term -/
  res₁ : InjectiveResolution S.X₁
  /-- Chosen injective resolution of the middle term -/
  res₂ : InjectiveResolution S.X₂
  /-- Chosen injective resolution of the right term -/
  res₃ : InjectiveResolution S.X₃
  /-- Lift of `S.f` to the resolution complexes -/
  φf : res₁.cocomplex ⟶ res₂.cocomplex
  /-- Lift of `S.g` to the resolution complexes -/
  φg : res₂.cocomplex ⟶ res₃.cocomplex
  /-- The lifts form a complex -/
  w : φf ≫ φg = 0
  /-- `φf` lifts `S.f` through the augmentations -/
  lift_f : res₁.ι.f 0 ≫ φf.f 0 = S.f ≫ res₂.ι.f 0
  /-- `φg` lifts `S.g` through the augmentations -/
  lift_g : res₂.ι.f 0 ≫ φg.f 0 = S.g ≫ res₃.ι.f 0
  /-- The diagram of resolutions is degreewise split -/
  split : ∀ n, ((HomologicalComplex.eval C (ComplexShape.up ℕ) n).mapShortComplex.obj
    (ShortComplex.mk φf φg w)).Splitting

variable {S : ShortComplex C} {hS : S.ShortExact}

/-- The diagram of injective-resolution complexes determined by the lifts. -/
noncomputable def HorseshoeData.diagram (H : HorseshoeData S hS) :
    ShortComplex (CochainComplex C ℕ) :=
  ShortComplex.mk H.φf H.φg H.w

omit [HasInjectiveResolutions C] in
@[simp]
lemma HorseshoeData.diagram_f (H : HorseshoeData S hS) : H.diagram.f = H.φf :=
  rfl

omit [HasInjectiveResolutions C] in
@[simp]
lemma HorseshoeData.diagram_g (H : HorseshoeData S hS) : H.diagram.g = H.φg :=
  rfl

/-- The diagram after applying the additive functor `F`. -/
noncomputable def HorseshoeData.mapped (H : HorseshoeData S hS)
    (F : C ⥤ D) [F.Additive] : ShortComplex (CochainComplex D ℕ) :=
  H.diagram.map (F.mapHomologicalComplex (ComplexShape.up ℕ))

omit [HasInjectiveResolutions C] in
/-- The resolution diagram is itself short exact: it is degreewise split. -/
lemma HorseshoeData.diagram_shortExact (H : HorseshoeData S hS) :
    H.diagram.ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  have h := (H.split n).shortExact
  rwa [Functor.mapShortComplex_obj] at h

omit [HasInjectiveResolutions C] in
/-- An additive functor sends the degreewise split resolution diagram to a
short exact sequence of complexes. -/
lemma HorseshoeData.mapped_shortExact (H : HorseshoeData S hS)
    (F : C ⥤ D) [F.Additive] : (H.mapped F).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  -- The mapped splitting lives on `(diagram.map eval).map F`; the goal lives on
  -- `(mapped F).map eval`. Both unfold (up to the definitional commutation of
  -- evaluation with `mapHomologicalComplex`) to the same short complex, so
  -- `exact` closes the goal by definitional unfolding (`rfl`-level commutation
  -- plus proof irrelevance for the `PreservesZeroMorphisms` instances, which is
  -- why `rw` with the functor equality cannot be used here instead).
  have hsplit := ((H.split n).map F).shortExact
  simp only [Functor.mapShortComplex_obj, HorseshoeData.diagram,
    HorseshoeData.mapped, ← ShortComplex.map_comp] at hsplit ⊢
  exact hsplit

/-- The connecting morphism
`(F.rightDerived n₀).obj S.X₃ ⟶ (F.rightDerived n₁).obj S.X₁`. -/
noncomputable def HorseshoeData.delta (H : HorseshoeData S hS)
    (F : C ⥤ D) [F.Additive] (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    (F.rightDerived n₀).obj S.X₃ ⟶ (F.rightDerived n₁).obj S.X₁ :=
  (H.res₃.isoRightDerivedObj F n₀).hom ≫
    ((H.mapped_shortExact F).δ n₀ n₁ h) ≫
      (H.res₁.isoRightDerivedObj F n₁).inv

/-- The homology-level five-arrow window, used as the exact reference for the
transfer to `rightDerived` terms. -/
noncomputable def HorseshoeData.homologySequence (H : HorseshoeData S hS)
    (F : C ⥤ D) [F.Additive] (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    ComposableArrows D 5 :=
  HomologySequence.composableArrows₅ (H.mapped_shortExact F) n₀ n₁ h

omit [HasInjectiveResolutions C] in
/-- Exactness at the homology level, by the homology long exact sequence. -/
lemma HorseshoeData.homologySequence_exact (H : HorseshoeData S hS)
    (F : C ⥤ D) [F.Additive] (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    (H.homologySequence F n₀ n₁ h).Exact :=
  HomologySequence.composableArrows₅_exact (H.mapped_shortExact F) n₀ n₁ h

/-- The five-arrow window of the long exact sequence in `rightDerived` terms:
`Rⁿ⁰F X₁ ⟶ Rⁿ⁰F X₂ ⟶ Rⁿ⁰F X₃ ⟶ Rⁿ¹F X₁ ⟶ Rⁿ¹F X₂ ⟶ Rⁿ¹F X₃`. -/
noncomputable def HorseshoeData.longSequence (H : HorseshoeData S hS)
    (F : C ⥤ D) [F.Additive] (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    ComposableArrows D 5 :=
  ComposableArrows.mk₅ ((F.rightDerived n₀).map S.f) ((F.rightDerived n₀).map S.g)
    (H.delta F n₀ n₁ h) ((F.rightDerived n₁).map S.f)
    ((F.rightDerived n₁).map S.g)

/-- Comparison isomorphism between the homology-level and `rightDerived`
five-arrow windows. -/
noncomputable def HorseshoeData.sequenceIso (H : HorseshoeData S hS)
    (F : C ⥤ D) [F.Additive] (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    H.homologySequence F n₀ n₁ h ≅ H.longSequence F n₀ n₁ h := by
  refine ComposableArrows.isoMk₅ (H.res₁.isoRightDerivedObj F n₀).symm
    (H.res₂.isoRightDerivedObj F n₀).symm (H.res₃.isoRightDerivedObj F n₀).symm
    (H.res₁.isoRightDerivedObj F n₁).symm (H.res₂.isoRightDerivedObj F n₁).symm
    (H.res₃.isoRightDerivedObj F n₁).symm ?_ ?_ ?_ ?_ ?_
  · have hnat := InjectiveResolution.isoRightDerivedObj_hom_naturality
      S.f H.res₁ H.res₂ H.φf H.lift_f F n₀
    simp only [Functor.comp_map, HomologicalComplex.homologyFunctor_map] at hnat
    -- The goal is stated with `ComposableArrows.map'` projections, which are
    -- definitionally (by `rfl`) the underlying arrows; `show` exposes them.
    change homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map H.φf) n₀ ≫
        (H.res₂.isoRightDerivedObj F n₀).inv =
      (H.res₁.isoRightDerivedObj F n₀).inv ≫ (F.rightDerived n₀).map S.f
    exact (CommSq.horiz_inv (f := H.res₁.isoRightDerivedObj F n₀)
      (i := H.res₂.isoRightDerivedObj F n₀) ⟨hnat.symm⟩).w.symm
  · have hnat := InjectiveResolution.isoRightDerivedObj_hom_naturality
      S.g H.res₂ H.res₃ H.φg H.lift_g F n₀
    simp only [Functor.comp_map, HomologicalComplex.homologyFunctor_map] at hnat
    change homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map H.φg) n₀ ≫
        (H.res₃.isoRightDerivedObj F n₀).inv =
      (H.res₂.isoRightDerivedObj F n₀).inv ≫ (F.rightDerived n₀).map S.g
    exact (CommSq.horiz_inv (f := H.res₂.isoRightDerivedObj F n₀)
      (i := H.res₃.isoRightDerivedObj F n₀) ⟨hnat.symm⟩).w.symm
  · change ((H.mapped_shortExact F).δ n₀ n₁ h) ≫
        (H.res₁.isoRightDerivedObj F n₁).inv =
      (H.res₃.isoRightDerivedObj F n₀).inv ≫ H.delta F n₀ n₁ h
    rw [HorseshoeData.delta, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    exact rfl
  · have hnat := InjectiveResolution.isoRightDerivedObj_hom_naturality
      S.f H.res₁ H.res₂ H.φf H.lift_f F n₁
    simp only [Functor.comp_map, HomologicalComplex.homologyFunctor_map] at hnat
    change homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map H.φf) n₁ ≫
        (H.res₂.isoRightDerivedObj F n₁).inv =
      (H.res₁.isoRightDerivedObj F n₁).inv ≫ (F.rightDerived n₁).map S.f
    exact (CommSq.horiz_inv (f := H.res₁.isoRightDerivedObj F n₁)
      (i := H.res₂.isoRightDerivedObj F n₁) ⟨hnat.symm⟩).w.symm
  · have hnat := InjectiveResolution.isoRightDerivedObj_hom_naturality
      S.g H.res₂ H.res₃ H.φg H.lift_g F n₁
    simp only [Functor.comp_map, HomologicalComplex.homologyFunctor_map] at hnat
    change homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map H.φg) n₁ ≫
        (H.res₃.isoRightDerivedObj F n₁).inv =
      (H.res₂.isoRightDerivedObj F n₁).inv ≫ (F.rightDerived n₁).map S.g
    exact (CommSq.horiz_inv (f := H.res₂.isoRightDerivedObj F n₁)
      (i := H.res₃.isoRightDerivedObj F n₁) ⟨hnat.symm⟩).w.symm

/-- Exactness of the five-arrow window in `rightDerived` terms. -/
lemma HorseshoeData.longSequence_exact (H : HorseshoeData S hS)
    (F : C ⥤ D) [F.Additive] (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    (H.longSequence F n₀ n₁ h).Exact :=
  ComposableArrows.exact_of_iso (H.sequenceIso F n₀ n₁ h)
    (H.homologySequence_exact F n₀ n₁ h)

/-- A morphism of horseshoe data over a morphism `α` of short exact
sequences: lifts of the three components commuting with the resolution
maps. -/
@[ext]
structure HorseshoeData.Hom {S₁ S₂ : ShortComplex C}
    {hS₁ : S₁.ShortExact} {hS₂ : S₂.ShortExact}
    (H₁ : HorseshoeData S₁ hS₁) (H₂ : HorseshoeData S₂ hS₂)
    (α : S₁ ⟶ S₂) where
  /-- Lift of `α.τ₁` to the left resolutions -/
  ψ₁ : H₁.res₁.cocomplex ⟶ H₂.res₁.cocomplex
  /-- Lift of `α.τ₂` to the middle resolutions -/
  ψ₂ : H₁.res₂.cocomplex ⟶ H₂.res₂.cocomplex
  /-- Lift of `α.τ₃` to the right resolutions -/
  ψ₃ : H₁.res₃.cocomplex ⟶ H₂.res₃.cocomplex
  /-- `ψ₁` lifts `α.τ₁` through the augmentations -/
  lift₁ : H₁.res₁.ι.f 0 ≫ ψ₁.f 0 = α.τ₁ ≫ H₂.res₁.ι.f 0
  /-- `ψ₂` lifts `α.τ₂` through the augmentations -/
  lift₂ : H₁.res₂.ι.f 0 ≫ ψ₂.f 0 = α.τ₂ ≫ H₂.res₂.ι.f 0
  /-- `ψ₃` lifts `α.τ₃` through the augmentations -/
  lift₃ : H₁.res₃.ι.f 0 ≫ ψ₃.f 0 = α.τ₃ ≫ H₂.res₃.ι.f 0
  /-- Compatibility with the left resolution maps -/
  comm_φf : H₁.φf ≫ ψ₂ = ψ₁ ≫ H₂.φf
  /-- Compatibility with the right resolution maps -/
  comm_φg : H₁.φg ≫ ψ₃ = ψ₂ ≫ H₂.φg

variable {S₁ S₂ : ShortComplex C} {hS₁ : S₁.ShortExact} {hS₂ : S₂.ShortExact}
  {H₁ : HorseshoeData S₁ hS₁} {H₂ : HorseshoeData S₂ hS₂}
  {α : S₁ ⟶ S₂}

/-- The induced morphism between the mapped short exact sequences of
complexes. -/
noncomputable def HorseshoeData.Hom.mappedHom
    (e : HorseshoeData.Hom H₁ H₂ α)
    (F : C ⥤ D) [F.Additive] : (H₁.mapped F) ⟶ (H₂.mapped F) := by
  refine ShortComplex.homMk ?_ ?_ ?_ ?_ ?_
  · exact (F.mapHomologicalComplex (ComplexShape.up ℕ)).map e.ψ₁
  · exact (F.mapHomologicalComplex (ComplexShape.up ℕ)).map e.ψ₂
  · exact (F.mapHomologicalComplex (ComplexShape.up ℕ)).map e.ψ₃
  · change (F.mapHomologicalComplex (ComplexShape.up ℕ)).map e.ψ₁ ≫
        (F.mapHomologicalComplex (ComplexShape.up ℕ)).map H₂.φf =
      (F.mapHomologicalComplex (ComplexShape.up ℕ)).map H₁.φf ≫
        (F.mapHomologicalComplex (ComplexShape.up ℕ)).map e.ψ₂
    rw [← Functor.map_comp, ← Functor.map_comp, e.comm_φf]
  · change (F.mapHomologicalComplex (ComplexShape.up ℕ)).map e.ψ₂ ≫
        (F.mapHomologicalComplex (ComplexShape.up ℕ)).map H₂.φg =
      (F.mapHomologicalComplex (ComplexShape.up ℕ)).map H₁.φg ≫
        (F.mapHomologicalComplex (ComplexShape.up ℕ)).map e.ψ₃
    rw [← Functor.map_comp, ← Functor.map_comp, e.comm_φg]

/-- Naturality of the connecting morphism in morphisms of horseshoe data. -/
lemma HorseshoeData.Hom.delta_naturality
    (e : HorseshoeData.Hom H₁ H₂ α)
    (F : C ⥤ D) [F.Additive] (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    (H₁.delta F n₀ n₁ h) ≫ (F.rightDerived n₁).map α.τ₁ =
      (F.rightDerived n₀).map α.τ₃ ≫ (H₂.delta F n₀ n₁ h) := by
  have hnat₁ := InjectiveResolution.isoRightDerivedObj_hom_naturality
    α.τ₁ H₁.res₁ H₂.res₁ e.ψ₁ e.lift₁ F n₁
  have hnat₃ := InjectiveResolution.isoRightDerivedObj_hom_naturality
    α.τ₃ H₁.res₃ H₂.res₃ e.ψ₃ e.lift₃ F n₀
  have hδ := HomologySequence.δ_naturality (e.mappedHom F)
    (H₁.mapped_shortExact F) (H₂.mapped_shortExact F) n₀ n₁ h
  simp only [Functor.comp_map, HomologicalComplex.homologyFunctor_map] at hnat₁ hnat₃
  have hnat₁' : (H₁.res₁.isoRightDerivedObj F n₁).inv ≫
      (F.rightDerived n₁).map α.τ₁ =
      homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map e.ψ₁) n₁ ≫
        (H₂.res₁.isoRightDerivedObj F n₁).inv :=
    (CommSq.horiz_inv (f := H₁.res₁.isoRightDerivedObj F n₁)
      (i := H₂.res₁.isoRightDerivedObj F n₁) ⟨hnat₁.symm⟩).w
  have hδ' : ((H₁.mapped_shortExact F).δ n₀ n₁ h) ≫
      homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map e.ψ₁) n₁ =
      homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map e.ψ₃) n₀ ≫
        ((H₂.mapped_shortExact F).δ n₀ n₁ h) := by
    have hδ'' := hδ
    simp only [HorseshoeData.Hom.mappedHom] at hδ''
    exact hδ''
  calc
    H₁.delta F n₀ n₁ h ≫ (F.rightDerived n₁).map α.τ₁ =
        (H₁.res₃.isoRightDerivedObj F n₀).hom ≫
          (H₁.mapped_shortExact F).δ n₀ n₁ h ≫
            ((H₁.res₁.isoRightDerivedObj F n₁).inv ≫
              (F.rightDerived n₁).map α.τ₁) :=
      (Category.assoc (H₁.res₃.isoRightDerivedObj F n₀).hom
        ((H₁.mapped_shortExact F).δ n₀ n₁ h ≫ (H₁.res₁.isoRightDerivedObj F n₁).inv)
        ((F.rightDerived n₁).map α.τ₁)).trans
        (congrArg ((H₁.res₃.isoRightDerivedObj F n₀).hom ≫ ·)
          (Category.assoc ((H₁.mapped_shortExact F).δ n₀ n₁ h)
            (H₁.res₁.isoRightDerivedObj F n₁).inv ((F.rightDerived n₁).map α.τ₁)))
    _ = (H₁.res₃.isoRightDerivedObj F n₀).hom ≫
          (H₁.mapped_shortExact F).δ n₀ n₁ h ≫
            (homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map e.ψ₁) n₁ ≫
              (H₂.res₁.isoRightDerivedObj F n₁).inv) :=
      congrArg ((H₁.res₃.isoRightDerivedObj F n₀).hom ≫
        (H₁.mapped_shortExact F).δ n₀ n₁ h ≫ ·) hnat₁'
    _ = (H₁.res₃.isoRightDerivedObj F n₀).hom ≫
          ((H₁.mapped_shortExact F).δ n₀ n₁ h ≫
            homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map e.ψ₁) n₁) ≫
              (H₂.res₁.isoRightDerivedObj F n₁).inv :=
      congrArg ((H₁.res₃.isoRightDerivedObj F n₀).hom ≫ ·)
        (Category.assoc ((H₁.mapped_shortExact F).δ n₀ n₁ h)
          (homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map e.ψ₁) n₁)
          (H₂.res₁.isoRightDerivedObj F n₁).inv).symm
    _ = (H₁.res₃.isoRightDerivedObj F n₀).hom ≫
          (homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map e.ψ₃) n₀ ≫
            (H₂.mapped_shortExact F).δ n₀ n₁ h) ≫
              (H₂.res₁.isoRightDerivedObj F n₁).inv :=
      congrArg ((H₁.res₃.isoRightDerivedObj F n₀).hom ≫ · ≫
        (H₂.res₁.isoRightDerivedObj F n₁).inv) hδ'
    _ = ((H₁.res₃.isoRightDerivedObj F n₀).hom ≫
          homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map e.ψ₃) n₀) ≫
            (H₂.mapped_shortExact F).δ n₀ n₁ h ≫
              (H₂.res₁.isoRightDerivedObj F n₁).inv :=
      (congrArg ((H₁.res₃.isoRightDerivedObj F n₀).hom ≫ ·)
        (Category.assoc
          (homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map e.ψ₃) n₀)
          ((H₂.mapped_shortExact F).δ n₀ n₁ h)
          (H₂.res₁.isoRightDerivedObj F n₁).inv)).trans
        (Category.assoc (H₁.res₃.isoRightDerivedObj F n₀).hom
          (homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map e.ψ₃) n₀)
          ((H₂.mapped_shortExact F).δ n₀ n₁ h ≫
            (H₂.res₁.isoRightDerivedObj F n₁).inv)).symm
    _ = ((F.rightDerived n₀).map α.τ₃ ≫ (H₂.res₃.isoRightDerivedObj F n₀).hom) ≫
          (H₂.mapped_shortExact F).δ n₀ n₁ h ≫
            (H₂.res₁.isoRightDerivedObj F n₁).inv :=
      congrArg (· ≫ (H₂.mapped_shortExact F).δ n₀ n₁ h ≫
        (H₂.res₁.isoRightDerivedObj F n₁).inv) hnat₃.symm
    _ = (F.rightDerived n₀).map α.τ₃ ≫ H₂.delta F n₀ n₁ h :=
      Category.assoc ((F.rightDerived n₀).map α.τ₃)
        (H₂.res₃.isoRightDerivedObj F n₀).hom
        ((H₂.mapped_shortExact F).δ n₀ n₁ h ≫
          (H₂.res₁.isoRightDerivedObj F n₁).inv)

/-- The induced morphism between the long exact sequences. On each object it
is `(F.rightDerived _).map` applied to the corresponding component of `α`. -/
noncomputable def HorseshoeData.Hom.longSequenceHom
    (e : HorseshoeData.Hom H₁ H₂ α)
    (F : C ⥤ D) [F.Additive] (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    (H₁.longSequence F n₀ n₁ h) ⟶ (H₂.longSequence F n₀ n₁ h) := by
  refine ComposableArrows.homMk₅ ((F.rightDerived n₀).map α.τ₁)
    ((F.rightDerived n₀).map α.τ₂) ((F.rightDerived n₀).map α.τ₃)
    ((F.rightDerived n₁).map α.τ₁) ((F.rightDerived n₁).map α.τ₂)
    ((F.rightDerived n₁).map α.τ₃) ?_ ?_ ?_ ?_ ?_
  · change (F.rightDerived n₀).map S₁.f ≫ (F.rightDerived n₀).map α.τ₂ =
      (F.rightDerived n₀).map α.τ₁ ≫ (F.rightDerived n₀).map S₂.f
    rw [← Functor.map_comp, ← Functor.map_comp, α.comm₁₂]
  · change (F.rightDerived n₀).map S₁.g ≫ (F.rightDerived n₀).map α.τ₃ =
      (F.rightDerived n₀).map α.τ₂ ≫ (F.rightDerived n₀).map S₂.g
    rw [← Functor.map_comp, ← Functor.map_comp, α.comm₂₃]
  · change H₁.delta F n₀ n₁ h ≫ (F.rightDerived n₁).map α.τ₁ =
      (F.rightDerived n₀).map α.τ₃ ≫ H₂.delta F n₀ n₁ h
    exact e.delta_naturality F n₀ n₁ h
  · change (F.rightDerived n₁).map S₁.f ≫ (F.rightDerived n₁).map α.τ₂ =
      (F.rightDerived n₁).map α.τ₁ ≫ (F.rightDerived n₁).map S₂.f
    rw [← Functor.map_comp, ← Functor.map_comp, α.comm₁₂]
  · change (F.rightDerived n₁).map S₁.g ≫ (F.rightDerived n₁).map α.τ₃ =
      (F.rightDerived n₁).map α.τ₂ ≫ (F.rightDerived n₁).map S₂.g
    rw [← Functor.map_comp, ← Functor.map_comp, α.comm₂₃]

section Endpoints

variable (S : ShortComplex C) (hS : S.ShortExact)
  (I₁ : InjectiveResolution S.X₁) (I₃ : InjectiveResolution S.X₃)

/-- Compatible resolution data from the injective horseshoe with prescribed
endpoint resolutions. Its middle resolution and its two cochain maps are
the existing horseshoe data without any replacement or comparison choices. -/
noncomputable def HorseshoeData.ofEndpoints : HorseshoeData S hS where
  res₁ := I₁
  res₂ := (InjectiveResolution.horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).middle
  res₃ := I₃
  φf := (InjectiveResolution.horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).i
  φg := (InjectiveResolution.horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).p
  w := (InjectiveResolution.horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).zero
  lift_f := InjectiveResolution.horseshoe_i_comm
    (hS := hS) (I₁ := I₁) (I₃ := I₃)
  lift_g := InjectiveResolution.horseshoe_p_comm
    (hS := hS) (I₁ := I₁) (I₃ := I₃)
  split := fun n => by
    let H := InjectiveResolution.horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)
    let e := InjectiveResolution.horseshoeMiddleXIso
      (hS := hS) (I₁ := I₁) (I₃ := I₃) n
    let S₀ : ShortComplex C := ShortComplex.mk
      (biprod.inl : I₁.cocomplex.X n ⟶ I₁.cocomplex.X n ⊞ I₃.cocomplex.X n)
      (biprod.snd : I₁.cocomplex.X n ⊞ I₃.cocomplex.X n ⟶ I₃.cocomplex.X n)
      (by simp)
    have hi : H.i.f n = biprod.inl ≫ e.inv := by
      rw [← InjectiveResolution.horseshoe_i_f
        (hS := hS) (I₁ := I₁) (I₃ := I₃) n,
        Category.assoc, Iso.hom_inv_id, Category.comp_id]
    have eS : S₀ ≅
        (ShortComplex.mk H.i H.p H.zero).map
          (HomologicalComplex.eval C (ComplexShape.up ℕ) n) :=
      ShortComplex.isoMk (Iso.refl _) e.symm (Iso.refl _) (by
        change 𝟙 _ ≫ H.i.f n = biprod.inl ≫ e.inv
        simpa only [Category.id_comp] using hi) (by
        change e.inv ≫ H.p.f n = biprod.snd ≫ 𝟙 _
        simpa only [Category.comp_id] using
          (InjectiveResolution.horseshoe_p_f
            (hS := hS) (I₁ := I₁) (I₃ := I₃) n))
    exact (ShortComplex.Splitting.ofHasBinaryBiproduct
      (I₁.cocomplex.X n) (I₃.cocomplex.X n)).ofIso eS

omit [HasInjectiveResolutions C] in
@[simp]
lemma HorseshoeData.ofEndpoints_res₁ : (HorseshoeData.ofEndpoints S hS I₁ I₃).res₁ = I₁ := rfl

omit [HasInjectiveResolutions C] in
@[simp]
lemma HorseshoeData.ofEndpoints_res₂ :
    (HorseshoeData.ofEndpoints S hS I₁ I₃).res₂ =
      (InjectiveResolution.horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).middle := rfl

omit [HasInjectiveResolutions C] in
@[simp]
lemma HorseshoeData.ofEndpoints_res₃ : (HorseshoeData.ofEndpoints S hS I₁ I₃).res₃ = I₃ := rfl

omit [HasInjectiveResolutions C] in
@[simp]
lemma HorseshoeData.ofEndpoints_φf :
    (HorseshoeData.ofEndpoints S hS I₁ I₃).φf =
      (InjectiveResolution.horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).i := rfl

omit [HasInjectiveResolutions C] in
@[simp]
lemma HorseshoeData.ofEndpoints_φg :
    (HorseshoeData.ofEndpoints S hS I₁ I₃).φg =
      (InjectiveResolution.horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).p := rfl

end Endpoints

end Functor.RightDerived

end CategoryTheory
