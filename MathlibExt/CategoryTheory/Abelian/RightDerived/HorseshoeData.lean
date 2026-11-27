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
# Right-derived long exact sequences from compatible injective resolutions

In an abelian category `C`, compatible injective horseshoe data for
`X₁ → X₂ → X₃` consists of three injective resolutions, coaugmentation-
compatible lifts of the two maps, and a splitting in every cochain degree.
An additive functor `F : C → D` into an abelian category sends this
diagram to a short exact sequence of complexes. If `C` has injective
resolutions, comparison with `R^nF` transports its cohomology long exact
sequence to right-derived terms. Maps of compatible data give the
connecting and long-sequence naturality squares.

The middle resolution and degreewise splittings are arbitrary compatible
choices; the injective horseshoe with prescribed endpoints supplies
one such choice.
-/

@[expose] public section

namespace CategoryTheory

open Category Limits HomologicalComplex

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasInjectiveResolutions C]
variable {D : Type u₂} [Category.{v₂} D] [Abelian D]

namespace Functor.RightDerived

/-- For a short exact sequence `S : X₁ → X₂ → X₃` in an abelian
category `C`, compatible horseshoe data consists of injective resolutions
`I₁,I₂,I₃`, cochain maps lifting the two sequence maps and preserving
their coaugmentations, a zero composite, and a splitting of
`I₁^n → I₂^n → I₃^n` for every `n ∈ ℕ`. -/
@[ext]
structure HorseshoeData (S : ShortComplex C) (hS : S.ShortExact) where
  /-- For a short exact sequence `S : X₁ → X₂ → X₃` in an abelian
category `C`, the left object of the horseshoe data is a chosen injective
cochain resolution `I₁` of `X₁`, with coaugmentation `X₁[0] → I₁`. -/
  res₁ : InjectiveResolution S.X₁
  /-- For a short exact sequence `S : X₁ → X₂ → X₃` in an abelian
category `C`, the middle object of the horseshoe data is a chosen injective
cochain resolution `I₂` of `X₂`, with coaugmentation `X₂[0] → I₂`. -/
  res₂ : InjectiveResolution S.X₂
  /-- For a short exact sequence `S : X₁ → X₂ → X₃` in an abelian
category `C`, the right object of the horseshoe data is a chosen injective
cochain resolution `I₃` of `X₃`, with coaugmentation `X₃[0] → I₃`. -/
  res₃ : InjectiveResolution S.X₃
  /-- For a short exact sequence `S : X₁ → X₂ → X₃` in an abelian
category `C`, the left sequence map is lifted to a cochain map
`φ_f : I₁ → I₂` between the chosen injective resolutions. -/
  φf : res₁.cocomplex ⟶ res₂.cocomplex
  /-- For a short exact sequence `S : X₁ → X₂ → X₃` in an abelian
category `C`, the right sequence map is lifted to a cochain map
`φ_g : I₂ → I₃` between the chosen injective resolutions. -/
  φg : res₂.cocomplex ⟶ res₃.cocomplex
  /-- For a short exact sequence `S : X₁ → X₂ → X₃` in an abelian
category `C`, the chosen cochain lifts `φ_f : I₁ → I₂`, `φ_g : I₂ → I₃`
have zero composite, so they form a short complex of resolutions. -/
  w : φf ≫ φg = 0
  /-- For a short exact sequence `S : X₁ → X₂ → X₃` in an abelian
category `C`, the left lift satisfies the degree-zero coaugmentation
square `ι₁⁰ ≫ φ_f⁰ = S.f ≫ ι₂⁰`. -/
  lift_f : res₁.ι.f 0 ≫ φf.f 0 = S.f ≫ res₂.ι.f 0
  /-- For a short exact sequence `S : X₁ → X₂ → X₃` in an abelian
category `C`, the right lift satisfies the degree-zero coaugmentation
square `ι₂⁰ ≫ φ_g⁰ = S.g ≫ ι₃⁰`. -/
  lift_g : res₂.ι.f 0 ≫ φg.f 0 = S.g ≫ res₃.ι.f 0
  /-- For a short exact sequence `S : X₁ → X₂ → X₃` in an abelian
category `C`, the resolution row `I₁^n → I₂^n → I₃^n` has a chosen
splitting in `C` for every nonnegative degree `n`. -/
  split : ∀ n, ((HomologicalComplex.eval C (ComplexShape.up ℕ) n).mapShortComplex.obj
    (ShortComplex.mk φf φg w)).Splitting

variable {S : ShortComplex C} {hS : S.ShortExact}

/-- Let `C` be abelian and `H` be compatible injective horseshoe
data for short exact `S : X₁ → X₂ → X₃`, with degreewise split
resolution diagram `I₁ → I₂ → I₃`. The chosen cochain lifts and their zero composite form the
short complex of nonnegative cochain complexes `I₁ → I₂ → I₃`. -/
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

/-- Let `C` be abelian and `H` be compatible injective horseshoe
data for short exact `S : X₁ → X₂ → X₃`, with degreewise split
resolution diagram `I₁ → I₂ → I₃`. Let `D` be abelian and `F : C → D` additive. Applying `F` to each term and differential gives the short
complex `F(I₁) → F(I₂) → F(I₃)` of nonnegative cochain complexes in `D`. -/
noncomputable def HorseshoeData.mapped (H : HorseshoeData S hS)
    (F : C ⥤ D) [F.Additive] : ShortComplex (CochainComplex D ℕ) :=
  H.diagram.map (F.mapHomologicalComplex (ComplexShape.up ℕ))

omit [HasInjectiveResolutions C] in
/-- Let `C` be abelian and `H` be compatible injective horseshoe
data for short exact `S : X₁ → X₂ → X₃`, with degreewise split
resolution diagram `I₁ → I₂ → I₃`. The diagram `I₁ → I₂ → I₃` is a short exact sequence of
complexes because each of its degree rows is split exact. -/
lemma HorseshoeData.diagram_shortExact (H : HorseshoeData S hS) :
    H.diagram.ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  have h := (H.split n).shortExact
  rwa [Functor.mapShortComplex_obj] at h

omit [HasInjectiveResolutions C] in
/-- Let `C` be abelian and `H` be compatible injective horseshoe
data for short exact `S : X₁ → X₂ → X₃`, with degreewise split
resolution diagram `I₁ → I₂ → I₃`. Let `D` be abelian and `F : C → D` additive. The diagram `F(I₁) → F(I₂) → F(I₃)` is short exact because
additivity preserves its splitting in every degree. -/
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

/-- Let `C,D` be abelian, with injective resolutions in `C`,
`F : C → D` additive, and `H` compatible injective horseshoe data
for short exact `S : X₁ → X₂ → X₃`. For `n₁=n₀+1`, its cohomology boundary transported by the
resolution comparisons gives `R^n₀F(X₃) → R^n₁F(X₁)`. -/
noncomputable def HorseshoeData.delta (H : HorseshoeData S hS)
    (F : C ⥤ D) [F.Additive] (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    (F.rightDerived n₀).obj S.X₃ ⟶ (F.rightDerived n₁).obj S.X₁ :=
  (H.res₃.isoRightDerivedObj F n₀).hom ≫
    ((H.mapped_shortExact F).δ n₀ n₁ h) ≫
      (H.res₁.isoRightDerivedObj F n₁).inv

/-- Let `C` be abelian and `H` be compatible injective horseshoe
data for short exact `S : X₁ → X₂ → X₃`, with degreewise split
resolution diagram `I₁ → I₂ → I₃`. Let `D` be abelian and `F : C → D` additive. For `n₁=n₀+1`, the cohomology sequence has the five-arrow
window `H^n₀F(I₁) → H^n₀F(I₂) → H^n₀F(I₃) → H^n₁F(I₁) →
H^n₁F(I₂) → H^n₁F(I₃)`, with its middle map the connecting morphism. -/
noncomputable def HorseshoeData.homologySequence (H : HorseshoeData S hS)
    (F : C ⥤ D) [F.Additive] (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    ComposableArrows D 5 :=
  HomologySequence.composableArrows₅ (H.mapped_shortExact F) n₀ n₁ h

omit [HasInjectiveResolutions C] in
/-- Let `C` be abelian and `H` be compatible injective horseshoe
data for short exact `S : X₁ → X₂ → X₃`, with degreewise split
resolution diagram `I₁ → I₂ → I₃`. Let `D` be abelian and `F : C → D` additive. For `n₁=n₀+1`, the five-arrow cohomology window of the mapped
horseshoe is exact. Its middle map is the cohomology connecting morphism
from `H^n₀F(I₃)` to `H^n₁F(I₁)`. -/
lemma HorseshoeData.homologySequence_exact (H : HorseshoeData S hS)
    (F : C ⥤ D) [F.Additive] (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    (H.homologySequence F n₀ n₁ h).Exact :=
  HomologySequence.composableArrows₅_exact (H.mapped_shortExact F) n₀ n₁ h

/-- Let `C,D` be abelian, with injective resolutions in `C`,
`F : C → D` additive, and `H` compatible injective horseshoe data
for short exact `S : X₁ → X₂ → X₃`. For `n₁=n₀+1`, the derived long sequence has the window
`R^n₀F(X₁) → R^n₀F(X₂) → R^n₀F(X₃) → R^n₁F(X₁) →
R^n₁F(X₂) → R^n₁F(X₃)`. -/
noncomputable def HorseshoeData.longSequence (H : HorseshoeData S hS)
    (F : C ⥤ D) [F.Additive] (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    ComposableArrows D 5 :=
  ComposableArrows.mk₅ ((F.rightDerived n₀).map S.f) ((F.rightDerived n₀).map S.g)
    (H.delta F n₀ n₁ h) ((F.rightDerived n₁).map S.f)
    ((F.rightDerived n₁).map S.g)

/-- Let `C,D` be abelian, with injective resolutions in `C`,
`F : C → D` additive, and `H` compatible injective horseshoe data
for short exact `S : X₁ → X₂ → X₃`. For `n₁=n₀+1`, the three resolution comparisons in both
degrees give an isomorphism from the five-arrow cohomology window of
`F(I₁) → F(I₂) → F(I₃)` to its right-derived window. -/
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

/-- Let `C,D` be abelian, with injective resolutions in `C`,
`F : C → D` additive, and `H` compatible injective horseshoe data
for short exact `S : X₁ → X₂ → X₃`. For `n₁=n₀+1`, its five-arrow window in right-derived terms
is exact, by transport of the cohomology long exact sequence. -/
lemma HorseshoeData.longSequence_exact (H : HorseshoeData S hS)
    (F : C ⥤ D) [F.Additive] (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    (H.longSequence F n₀ n₁ h).Exact :=
  ComposableArrows.exact_of_iso (H.sequenceIso F n₀ n₁ h)
    (H.homologySequence_exact F n₀ n₁ h)

/-- For two compatible injective horseshoe data `H₁,H₂` in an
abelian category `C` over short exact sequences `S₁,S₂` and a
sequence map `α : S₁ → S₂`, a morphism of data consists of three cochain lifts of the
components of `α`, preserving their coaugmentations and commuting
with both resolution-sequence maps. -/
@[ext]
structure HorseshoeData.Hom {S₁ S₂ : ShortComplex C}
    {hS₁ : S₁.ShortExact} {hS₂ : S₂.ShortExact}
    (H₁ : HorseshoeData S₁ hS₁) (H₂ : HorseshoeData S₂ hS₂)
    (α : S₁ ⟶ S₂) where
  /-- For two compatible injective horseshoe data `H₁,H₂` in an
abelian category `C` over short exact sequences `S₁,S₂` and a
sequence map `α : S₁ → S₂`, the left component is a cochain map `ψ₁ : I₁ → I₁′`
lifting the map `α₁ : S₁.X₁ → S₂.X₁`. -/
  ψ₁ : H₁.res₁.cocomplex ⟶ H₂.res₁.cocomplex
  /-- For two compatible injective horseshoe data `H₁,H₂` in an
abelian category `C` over short exact sequences `S₁,S₂` and a
sequence map `α : S₁ → S₂`, the middle component is a cochain map `ψ₂ : I₂ → I₂′`
lifting the map `α₂ : S₁.X₂ → S₂.X₂`. -/
  ψ₂ : H₁.res₂.cocomplex ⟶ H₂.res₂.cocomplex
  /-- For two compatible injective horseshoe data `H₁,H₂` in an
abelian category `C` over short exact sequences `S₁,S₂` and a
sequence map `α : S₁ → S₂`, the right component is a cochain map `ψ₃ : I₃ → I₃′`
lifting the map `α₃ : S₁.X₃ → S₂.X₃`. -/
  ψ₃ : H₁.res₃.cocomplex ⟶ H₂.res₃.cocomplex
  /-- For two compatible injective horseshoe data `H₁,H₂` in an
abelian category `C` over short exact sequences `S₁,S₂` and a
sequence map `α : S₁ → S₂`, the left cochain lift satisfies the degree-zero equation
`ι₁⁰ ≫ ψ₁⁰ = α₁ ≫ ι₁′⁰`. -/
  lift₁ : H₁.res₁.ι.f 0 ≫ ψ₁.f 0 = α.τ₁ ≫ H₂.res₁.ι.f 0
  /-- For two compatible injective horseshoe data `H₁,H₂` in an
abelian category `C` over short exact sequences `S₁,S₂` and a
sequence map `α : S₁ → S₂`, the middle cochain lift satisfies the degree-zero equation
`ι₂⁰ ≫ ψ₂⁰ = α₂ ≫ ι₂′⁰`. -/
  lift₂ : H₁.res₂.ι.f 0 ≫ ψ₂.f 0 = α.τ₂ ≫ H₂.res₂.ι.f 0
  /-- For two compatible injective horseshoe data `H₁,H₂` in an
abelian category `C` over short exact sequences `S₁,S₂` and a
sequence map `α : S₁ → S₂`, the right cochain lift satisfies the degree-zero equation
`ι₃⁰ ≫ ψ₃⁰ = α₃ ≫ ι₃′⁰`. -/
  lift₃ : H₁.res₃.ι.f 0 ≫ ψ₃.f 0 = α.τ₃ ≫ H₂.res₃.ι.f 0
  /-- For two compatible injective horseshoe data `H₁,H₂` in an
abelian category `C` over short exact sequences `S₁,S₂` and a
sequence map `α : S₁ → S₂`, the component lifts satisfy the cochain square
`H₁.φ_f ≫ ψ₂ = ψ₁ ≫ H₂.φ_f`. -/
  comm_φf : H₁.φf ≫ ψ₂ = ψ₁ ≫ H₂.φf
  /-- For two compatible injective horseshoe data `H₁,H₂` in an
abelian category `C` over short exact sequences `S₁,S₂` and a
sequence map `α : S₁ → S₂`, the component lifts satisfy the cochain square
`H₁.φ_g ≫ ψ₃ = ψ₂ ≫ H₂.φ_g`. -/
  comm_φg : H₁.φg ≫ ψ₃ = ψ₂ ≫ H₂.φg

variable {S₁ S₂ : ShortComplex C} {hS₁ : S₁.ShortExact} {hS₂ : S₂.ShortExact}
  {H₁ : HorseshoeData S₁ hS₁} {H₂ : HorseshoeData S₂ hS₂}
  {α : S₁ ⟶ S₂}

/-- For two compatible injective horseshoe data `H₁,H₂` in an
abelian category `C` over short exact sequences `S₁,S₂` and a
sequence map `α : S₁ → S₂`, an additive `F : C → D` into an abelian category maps the
three cochain components to a morphism between the short exact
mapped horseshoe diagrams. -/
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

/-- For two compatible injective horseshoe data `H₁,H₂` in an
abelian category `C` over short exact sequences `S₁,S₂` and a
sequence map `α : S₁ → S₂`, with `C` admitting injective resolutions and additive
`F : C → D` into abelian `D`, its boundary squares satisfy
`δ_H₁ ≫ R^n₁F(α₁) = R^n₀F(α₃) ≫ δ_H₂` for `n₁=n₀+1`. -/
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

/-- For two compatible injective horseshoe data `H₁,H₂` in an
abelian category `C` over short exact sequences `S₁,S₂` and a
sequence map `α : S₁ → S₂`, with `C` admitting injective resolutions and additive
`F : C → D` into abelian `D`, the induced morphism between the
five-arrow derived windows has component `R^nF(α_k)` at each
endpoint and degree. -/
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

/-- In an abelian category `C`, let `S : X₁ → X₂ → X₃` be short exact
and fix injective resolutions `I₁,I₃` of its endpoints. The injective
horseshoe construction supplies compatible data with those endpoint
resolutions, a middle resolution of `X₂`, and split degree rows. -/
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
