/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
-- Original authors: @toskua, Avocado
module

public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.Opposite
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import Mathlib.CategoryTheory.Adjunction.Limits
public import MathlibExt.CategoryTheory.Abelian.Projective.Horseshoe
public import MathlibExt.CategoryTheory.Abelian.Injective.OpDuality

/-!
# The injective horseshoe lemma

Let `C` be an abelian category and let `S : X₁ → X₂ → X₃` be a short
exact sequence. Given injective resolutions `I₁` of `X₁` and `I₃` of `X₃`,
the horseshoe construction gives an injective resolution `H` of `X₂` and a
short exact sequence of cochain complexes `I₁ → H → I₃`, indexed by `ℕ`.
The augmentations commute with the two maps of `S`.

In degree `n`, the middle object identifies with `I₁ⁿ ⊞ I₃ⁿ`. The inclusion
and projection are the two biproduct maps, and the differential from degree
`n` to `n + 1` has matrix `[[d₁, κ], [0, d₃]]`. The construction is the
projective horseshoe construction in `Cᵒᵖ`, transported back to `C`.
-/

@[expose] public section

namespace CategoryTheory.InjectiveResolution

open CategoryTheory Limits

open scoped ZeroObject

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

/- Proof implementation note.
The op'd left-endpoint resolution, ascribed to the `ProjectiveResolution`
type with the exact baked instances (`Abelian.hasZeroObject`,
`Preadditive.preadditiveHasZeroMorphisms`) and object (`S.op.X₁`) that
`HorseshoeData`'s `P₁` slot carries. (Without ascription, `rw`/`simp` fail:
`injectiveResolutionOpProj` bakes `hasZeroMorphismsOpposite` over
`op S.X₃`, which is only default-transparency defeq to the slot type, while
tactics check at reducible transparency.)
-/

/-- For a short complex `S` in an abelian category `C` and an injective
resolution `I₃` of `S.X₃`, the opposite resolution is a projective resolution
of `S.op.X₁ = op S.X₃` in `Cᵒᵖ`. Its underlying chain complex is indexed
by `ℕ`, with the zero objects and zero morphisms supplied by the abelian structure. -/
noncomputable def opProjLeft {S : ShortComplex C} (I₃ : InjectiveResolution S.X₃) :
    @ProjectiveResolution Cᵒᵖ Category.opposite
      (@Abelian.hasZeroObject Cᵒᵖ Category.opposite inferInstance)
      (@Preadditive.preadditiveHasZeroMorphisms Cᵒᵖ Category.opposite
        (@Abelian.toPreadditive Cᵒᵖ Category.opposite inferInstance))
      S.op.X₁ :=
  injectiveResolutionOpProj I₃

/-- For a short complex `S` in an abelian category `C` and an injective
resolution `I₁` of `S.X₁`, the opposite resolution is a projective resolution
of `S.op.X₃ = op S.X₁` in `Cᵒᵖ`. This is the right endpoint resolution for
the opposite horseshoe sequence. -/
noncomputable def opProjRight {S : ShortComplex C} (I₁ : InjectiveResolution S.X₁) :
    @ProjectiveResolution Cᵒᵖ Category.opposite
      (@Abelian.hasZeroObject Cᵒᵖ Category.opposite inferInstance)
      (@Preadditive.preadditiveHasZeroMorphisms Cᵒᵖ Category.opposite
        (@Abelian.toPreadditive Cᵒᵖ Category.opposite inferInstance))
      S.op.X₃ :=
  injectiveResolutionOpProj I₁

/- Proof implementation note.
The `unopFunctor`-image of the op'd right-endpoint complex is the original
cocomplex (definitionally). Stated with `unopFunctor.obj` (rather than `.op`
followed by `.unop`) so all endpoint shapes are syntactically
`(down ℕ).symm`, keeping `rw`-matching sound (the `.unop` roundtrip shape
`((up ℕ).symm).symm` is only default-transparency defeq).
-/

/-- Let `C` be abelian, `S` a short complex in `C`, and `I₁` an injective
resolution of `S.X₁`. The chain complex of the opposite projective resolution
`opProjRight I₁`, transported from `Cᵒᵖ` back to `C` by the complex opposite
equivalence, is canonically isomorphic to `I₁.cocomplex`. The comparison is
between cochain complexes indexed by `ℕ`, with differential `n → n + 1`. -/
noncomputable def unopObjIsoR {S : ShortComplex C} (I₁ : InjectiveResolution S.X₁) :
    (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).obj
      (Opposite.op (opProjRight I₁).complex) ≅ I₁.cocomplex :=
  Iso.refl _

/-- Let `C` be abelian, `S` a short complex in `C`, and `I₃` an injective
resolution of `S.X₃`. Transporting the chain complex of `opProjLeft I₃` from
`Cᵒᵖ` back to `C` gives a cochain complex canonically isomorphic to
`I₃.cocomplex`, with the natural-index cochain shape `n → n + 1`. -/
noncomputable def unopObjIsoL {S : ShortComplex C} (I₃ : InjectiveResolution S.X₃) :
    (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).obj
      (Opposite.op (opProjLeft I₃).complex) ≅ I₃.cocomplex :=
  Iso.refl _

/-- For a short exact sequence `S : X₁ → X₂ → X₃` in an abelian category
`C` and injective endpoint resolutions `I₁` and `I₃`, horseshoe data consist
of an injective resolution of `X₂`, a short exact sequence of natural-index
cochain complexes `I₁ → middle → I₃`, and compatibility with both augmentations. -/
structure HorseshoeData {S : ShortComplex C} (hS : S.ShortExact)
    (I₁ : InjectiveResolution S.X₁) (I₃ : InjectiveResolution S.X₃) where
  /-- For horseshoe data attached to a short exact sequence `S` in an abelian
category `C` and endpoint injective resolutions `I₁`, `I₃`, the middle object
is an injective resolution of `S.X₂`. Its cochain complex lies between the
two endpoint resolution complexes. -/
  middle : InjectiveResolution S.X₂
  /-- For horseshoe data over a short exact sequence `S` in an abelian category
`C`, this cochain map includes the given resolution `I₁` of `S.X₁` into the
middle injective resolution of `S.X₂`. Its augmentation lies over `S.f`. -/
  i : I₁.cocomplex ⟶ middle.cocomplex
  /-- For horseshoe data over a short exact sequence `S` in an abelian category
`C`, this cochain map projects the middle resolution of `S.X₂` onto the
resolution `I₃` of `S.X₃`. Its augmentation lies over `S.g`. -/
  p : middle.cocomplex ⟶ I₃.cocomplex
  /-- In horseshoe data for `S` and endpoint injective resolutions in an abelian
category `C`, the composite `I₁.cocomplex → middle.cocomplex → I₃.cocomplex`
is the zero cochain map. Thus the two resolution maps form a short complex. -/
  zero : i ≫ p = 0
  /-- For horseshoe data in an abelian category `C`, the sequence of cochain
complexes `I₁.cocomplex → middle.cocomplex → I₃.cocomplex` is short exact.
Consequently its object sequence is exact in each natural-number degree. -/
  shortExact : (ShortComplex.mk i p zero).ShortExact
  /-- For horseshoe data over `S : X₁ → X₂ → X₃` in an abelian category `C`,
the augmentation of `I₁` followed by the inclusion equals the map induced
by `S.f` between complexes concentrated in degree zero followed by the
middle augmentation: `I₁.ι ≫ i = single₀(S.f) ≫ middle.ι`. -/
  i_augmentation :
    I₁.ι ≫ i = (CochainComplex.single₀ C).map S.f ≫ middle.ι
  /-- For horseshoe data over `S : X₁ → X₂ → X₃` in an abelian category `C`,
the middle augmentation followed by the projection equals the degree-zero
map induced by `S.g` followed by the augmentation of `I₃`:
`middle.ι ≫ p = single₀(S.g) ≫ I₃.ι`. -/
  p_augmentation :
    middle.ι ≫ p = (CochainComplex.single₀ C).map S.g ≫ I₃.ι

namespace HorseshoeData

variable {S : ShortComplex C} {hS : S.ShortExact}
  {I₁ : InjectiveResolution S.X₁} {I₃ : InjectiveResolution S.X₃}

/-- For a short exact sequence `S` in an abelian category `C` with endpoint
injective resolutions `I₁`, `I₃`, apply the projective horseshoe lemma in
`Cᵒᵖ` to the reversed sequence `op X₃ → op X₂ → op X₁`. The opposite of
`I₃` supplies its left projective endpoint and the opposite of `I₁` its right endpoint. -/
noncomputable def opHorseshoe : ProjectiveResolution.HorseshoeData hS.op
    (opProjLeft I₃)
    (opProjRight I₁) :=
  ProjectiveResolution.horseshoe hS.op _ _

/-- For a short exact sequence `S` in an abelian category `C` with injective
endpoint resolutions `I₁`, `I₃`, the opposite of the projective horseshoe
projection gives a cochain map from `I₁.cocomplex` to the transported middle
resolution complex. The endpoint comparison identifies its source with `I₁`. -/
noncomputable def horseshoeI : I₁.cocomplex ⟶
    (opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).middle.complex.unop :=
  (unopObjIsoR I₁).inv ≫
    (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
      (opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).p.op

/-- For a short exact sequence `S` in an abelian category `C` with injective
endpoint resolutions `I₁`, `I₃`, the opposite of the projective horseshoe
inclusion gives a cochain map from the transported middle resolution complex
to `I₃.cocomplex`, using the canonical comparison at that endpoint. -/
noncomputable def horseshoeP :
    (opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).middle.complex.unop ⟶ I₃.cocomplex :=
  (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
      (opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).i.op ≫
    (unopObjIsoL I₃).hom

/- Proof implementation note.
The unop'd horseshoe maps compose to zero (unop of the op-side `zero`).
The `rfl`-equations unfold `horseshoeI`/`horseshoeP` (rather than `simp only`,
whose equation-lemma unfolding breaks `rw`-matching on these op-transported
terms).
-/

/-- For the short exact sequence `S` and injective endpoints `I₁`, `I₃` in
an abelian category `C`, the transported horseshoe inclusion followed by its
projection is zero: `horseshoeI ≫ horseshoeP = 0` as cochain maps on `ℕ`. -/
theorem horseshoe_zero : horseshoeI (hS := hS) (I₁ := I₁) (I₃ := I₃) ≫
    horseshoeP (hS := hS) (I₁ := I₁) (I₃ := I₃) = 0 := by
  have := unopFunctor_preservesZeroMorphisms (C := C)
  have hmap : (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
          (opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).p.op ≫
        (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
          (opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).i.op = 0 := by
    rw [← Functor.map_comp, ← op_comp, (opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).zero,
      op_zero]
    simp
  have hi : horseshoeI (hS := hS) (I₁ := I₁) (I₃ := I₃) =
      (unopObjIsoR I₁).inv ≫
        (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
          (opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).p.op := rfl
  have hp : horseshoeP (hS := hS) (I₁ := I₁) (I₃ := I₃) =
      (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
          (opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).i.op ≫
        (unopObjIsoL I₃).hom := rfl
  -- Terms-only: `rw`/`simp` cannot see through the `(down ℕ).symm`-vs-`up ℕ`
  -- shape defeq, so reassociate by explicit `trans`/`congrArg` (elaborated at
  -- default transparency, where the defeq holds).
  have step1 : horseshoeI (hS := hS) (I₁ := I₁) (I₃ := I₃) ≫
          horseshoeP (hS := hS) (I₁ := I₁) (I₃ := I₃)
      = ((unopObjIsoR I₁).inv ≫
            (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
              (opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).p.op) ≫
          ((HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
              (opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).i.op ≫
            (unopObjIsoL I₃).hom) :=
    congrArg₂ (· ≫ ·) hi hp
  have step2 : ((unopObjIsoR I₁).inv ≫
            (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
              (opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).p.op) ≫
          ((HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
              (opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).i.op ≫
            (unopObjIsoL I₃).hom)
      = (unopObjIsoR I₁).inv ≫
          (((HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
              (opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).p.op ≫
            (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
              (opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).i.op) ≫
            (unopObjIsoL I₃).hom) :=
    (Category.assoc _ _ _).trans
      (congrArg ((unopObjIsoR I₁).inv ≫ ·) (Category.assoc _ _ _).symm)
  have step34 : (unopObjIsoR I₁).inv ≫
          (((HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
              (opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).p.op ≫
            (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
              (opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).i.op) ≫
            (unopObjIsoL I₃).hom) = (0 : I₁.cocomplex ⟶ I₃.cocomplex) :=
    (congrArg ((unopObjIsoR I₁).inv ≫ ·)
      (congrArg (· ≫ (unopObjIsoL I₃).hom) hmap)).trans
      ((congrArg ((unopObjIsoR I₁).inv ≫ ·) zero_comp).trans comp_zero)
  exact step1.trans (step2.trans step34)

/-- For a short exact sequence `S` in an abelian category `C` and injective
endpoint resolutions `I₁`, `I₃`, transport the opposite projective horseshoe
sequence to a short complex of natural-index cochain complexes in `C`.
Its endpoint objects are the transported opposite endpoint resolution complexes. -/
noncomputable def transportedSES : ShortComplex (CochainComplex C ℕ) :=
  ShortComplex.mk
    ((HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
      (opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).p.op)
    ((HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
      (opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).i.op)
    (by
      have := unopFunctor_preservesZeroMorphisms (C := C)
      have hmap : (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
              (opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).p.op ≫
            (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
              (opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).i.op = 0 := by
        rw [← Functor.map_comp, ← op_comp,
          (opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).zero, op_zero]
        simp
      exact hmap)

/-- For a short exact sequence `S` in an abelian category `C` and injective
endpoint resolutions `I₁`, `I₃`, the short complex obtained by transporting
the opposite projective horseshoe through the complex opposite equivalence
is short exact in the abelian category of natural-index cochain complexes. -/
theorem transported_shortExact : (transportedSES (hS := hS) (I₁ := I₁) (I₃ := I₃)).ShortExact := by
  have := unopFunctor_preservesZeroMorphisms (C := C)
  have := unopFunctor_preservesFiniteLimits (C := C)
  have := unopFunctor_preservesFiniteColimits (C := C)
  change (((ShortComplex.mk (opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).i
      (opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).p
      (opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).zero).op).map
    (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ))).ShortExact
  exact ((opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).shortExact.op.map_of_exact _)

/-- For a short exact sequence `S` in an abelian category `C` and injective
resolutions `I₁`, `I₃`, the horseshoe short complex with endpoints identified
as `I₁.cocomplex` and `I₃.cocomplex` is isomorphic to the transported
opposite projective horseshoe sequence. The middle comparison is the identity. -/
noncomputable def transportedIso :
    ShortComplex.mk (horseshoeI (hS := hS) (I₁ := I₁) (I₃ := I₃))
        (horseshoeP (hS := hS) (I₁ := I₁) (I₃ := I₃))
        (horseshoe_zero (hS := hS) (I₁ := I₁) (I₃ := I₃)) ≅
      transportedSES (hS := hS) (I₁ := I₁) (I₃ := I₃) :=
  ShortComplex.isoMk (unopObjIsoR I₁).symm (Iso.refl _)
    (unopObjIsoL I₃).symm
    (by
      change (unopObjIsoR I₁).symm.hom ≫
          (transportedSES (hS := hS) (I₁ := I₁) (I₃ := I₃)).f =
        horseshoeI (hS := hS) (I₁ := I₁) (I₃ := I₃) ≫ 𝟙 _
      have hi : horseshoeI (hS := hS) (I₁ := I₁) (I₃ := I₃) =
          (unopObjIsoR I₁).inv ≫
            (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
              (opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).p.op := rfl
      have hf : (transportedSES (hS := hS) (I₁ := I₁) (I₃ := I₃)).f =
          (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
            (opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).p.op := rfl
      have c1a : (unopObjIsoR I₁).symm.hom ≫
              (transportedSES (hS := hS) (I₁ := I₁) (I₃ := I₃)).f
          = (unopObjIsoR I₁).inv ≫
              (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
                (opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).p.op :=
        congrArg₂ (· ≫ ·) (Iso.symm_hom _) hf
      have c1b : (unopObjIsoR I₁).inv ≫
              (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
                (opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).p.op
          = horseshoeI (hS := hS) (I₁ := I₁) (I₃ := I₃) ≫ 𝟙 _ :=
        ((congrArg₂ (· ≫ ·) hi rfl).trans (Category.comp_id _)).symm
      exact c1a.trans c1b)
    (by
      change 𝟙 _ ≫ (transportedSES (hS := hS) (I₁ := I₁) (I₃ := I₃)).g =
        horseshoeP (hS := hS) (I₁ := I₁) (I₃ := I₃) ≫
          (unopObjIsoL I₃).symm.hom
      have hp : horseshoeP (hS := hS) (I₁ := I₁) (I₃ := I₃) =
          (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
              (opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).i.op ≫
            (unopObjIsoL I₃).hom := rfl
      have hg : (transportedSES (hS := hS) (I₁ := I₁) (I₃ := I₃)).g =
          (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
            (opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).i.op := rfl
      have c2a : 𝟙 _ ≫ (transportedSES (hS := hS) (I₁ := I₁) (I₃ := I₃)).g
          = (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
              (opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).i.op :=
        (congrArg₂ (· ≫ ·) rfl hg).trans (Category.id_comp _)
      have c2b : (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
              (opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).i.op
          = horseshoeP (hS := hS) (I₁ := I₁) (I₃ := I₃) ≫
              (unopObjIsoL I₃).symm.hom :=
        ((((congrArg₂ (· ≫ ·) hp (Iso.symm_hom _)).trans
          (Category.assoc _ _ _)).trans
          (congrArg ((HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
            (opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).i.op ≫ ·)
            (unopObjIsoL I₃).hom_inv_id)).trans
          (Category.comp_id _)).symm
      exact c2a.trans c2b)

/-- For a short exact sequence `S` in an abelian category `C` and injective
resolutions `I₁`, `I₃`, the transported inclusion and projection form a short
exact sequence `I₁.cocomplex → middle → I₃.cocomplex` of cochain complexes
indexed by `ℕ`. -/
theorem horseshoe_shortExact :
    (ShortComplex.mk (horseshoeI (hS := hS) (I₁ := I₁) (I₃ := I₃))
        (horseshoeP (hS := hS) (I₁ := I₁) (I₃ := I₃))
      (horseshoe_zero (hS := hS) (I₁ := I₁) (I₃ := I₃))).ShortExact :=
  ShortComplex.shortExact_of_iso (transportedIso (hS := hS) (I₁ := I₁) (I₃ := I₃)).symm
    (transported_shortExact (hS := hS) (I₁ := I₁) (I₃ := I₃))

/- Proof implementation note.
Bridge: the endpoint augmentation followed by the unop-identification
equals `single₀UnopIso` followed by the unop'd op-side augmentation.

Informal sketch: degreewise (`Hom.ext`). In degree `0` everything is an
identity (`rfl`-bridges for `comp_f`/`unopFunctor`-`f`/`opFunctor`-`f` and
the `π`-unfolding, `unop_comp`, `(·.op).unop`, `single₀OpIso_hom_f_zero`);
off degree `0` both sides are maps out of a zero object
(`IsZero.eq_of_src`).
-/

/-- Let `C` be abelian and `I` an injective resolution of `S.X₁`.
The augmentation `I.ι`, followed by the inverse comparison to the transported
opposite projective complex, equals the opposite projective augmentation
after the canonical identification of the degree-zero single-object complex. -/
theorem augmentation_bridge_right (I : InjectiveResolution S.X₁) :
    I.ι ≫ (unopObjIsoR I).inv =
      (single₀UnopIso (C := C) S.X₁).hom ≫
        (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
          (opProjRight I).π.op := by
  apply HomologicalComplex.Hom.ext
  funext n
  have b1 : ((I.ι ≫ (unopObjIsoR I).inv)).f n = I.ι.f n ≫ 𝟙 _ := rfl
  have b2 : (((single₀UnopIso (C := C) S.X₁).hom ≫
        (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
          (opProjRight I).π.op)).f n =
      (single₀UnopIso (C := C) S.X₁).hom.f n ≫
        (((HomologicalComplex.opFunctor C (ComplexShape.up ℕ)).map I.ι.op).f n ≫
          (single₀OpIso S.X₁).hom.f n).unop := rfl
  have b3 : (((HomologicalComplex.opFunctor C (ComplexShape.up ℕ)).map I.ι.op).f n) =
      (I.ι.f n).op := rfl
  by_cases hn : n = 0
  · subst hn
    have hU0 : (single₀UnopIso (C := C) S.X₁).hom.f 0 = 𝟙 _ := rfl
    have hO0 : (single₀OpIso S.X₁).hom.f 0 =
        𝟙 (Opposite.op (((CochainComplex.single₀ C).obj S.X₁).X 0)) :=
      single₀OpIso_hom_f_zero S.X₁
    -- Freshly elaborated (uniform instances), so `simp` fires here even
    -- though it cannot inside the `rw`-produced goal below.
    have hinner : ((I.ι.f 0).op ≫
          𝟙 (Opposite.op (((CochainComplex.single₀ C).obj S.X₁).X 0))).unop =
        I.ι.f 0 := by
      simp only [Category.comp_id, Quiver.Hom.unop_op]
    rw [b1, b2, b3, hU0, hO0]
    exact (Category.comp_id _).trans ((Category.id_comp _).symm.trans
      (congrArg (𝟙 _ ≫ ·) hinner).symm)
  · have hX1 : ((CochainComplex.single₀ C).obj S.X₁).X n = (0 : C) := by
      simp [CochainComplex.single₀, HomologicalComplex.single, hn]
    have hZ : IsZero (((CochainComplex.single₀ C).obj S.X₁).X n) :=
      hX1.symm ▸ isZero_zero C
    exact hZ.eq_of_src _ _

/- Proof implementation note.
Naturality of `single₀UnopIso` through `op`: pushing a `single₀`-map
through the unop-identification.

Informal sketch: degreewise (`Hom.ext`). In degree `0` both single₀-maps
are the underlying arrow (`single₀_map_f_zero`) and the iso components
are identities; off degree `0` both sides are maps out of a zero object.
-/

/-- For objects `X`, `Y` of an abelian category `C` and a map `f : X → Y`,
the canonical comparison between the transported opposite chain complex
concentrated in degree zero and the corresponding cochain complex is natural
in `f`. Transporting the opposite single-object map agrees with the cochain
single-object map after these endpoint comparisons. -/
theorem single₀UnopIso_naturality {X Y : C} (f : X ⟶ Y) :
    (single₀UnopIso (C := C) X).hom ≫
        (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
          (((ChainComplex.single₀ Cᵒᵖ).map f.op).op) =
      (CochainComplex.single₀ C).map f ≫
        (single₀UnopIso (C := C) Y).hom := by
  apply HomologicalComplex.Hom.ext
  funext n
  have c1 : (((single₀UnopIso (C := C) X).hom ≫
        (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
          (((ChainComplex.single₀ Cᵒᵖ).map f.op).op))).f n =
      (single₀UnopIso (C := C) X).hom.f n ≫
        (((ChainComplex.single₀ Cᵒᵖ).map f.op).f n).unop := rfl
  have c2 : (((CochainComplex.single₀ C).map f ≫
        (single₀UnopIso (C := C) Y).hom)).f n =
      (((CochainComplex.single₀ C).map f).f n ≫
        (single₀UnopIso (C := C) Y).hom.f n) := rfl
  by_cases hn : n = 0
  · subst hn
    have hUX : (single₀UnopIso (C := C) X).hom.f 0 = 𝟙 _ := rfl
    have hUY : (single₀UnopIso (C := C) Y).hom.f 0 = 𝟙 _ := rfl
    have hop : (f.op).unop = f := rfl
    -- Term-mode combination: `rw` on these goals trips over `(down ℕ).symm`
    -- vs `up ℕ` shape ascriptions (reducible-transparency mismatch), while
    -- elaboration-time unification (default transparency) is robust.
    have e1 : ((((ChainComplex.single₀ Cᵒᵖ).map f.op).f 0)).unop = f :=
      (congrArg Quiver.Hom.unop (ChainComplex.single₀_map_f_zero _)).trans hop
    have e2 : ((((CochainComplex.single₀ C).map f).f 0)) = f :=
      CochainComplex.single₀_map_f_zero _
    have a1 : (single₀UnopIso (C := C) X).hom.f 0 ≫
          ((((ChainComplex.single₀ Cᵒᵖ).map f.op).f 0)).unop = f :=
      (congrArg₂ (· ≫ ·) hUX e1).trans (Category.id_comp _)
    have a2 : (((CochainComplex.single₀ C).map f).f 0) ≫
          (single₀UnopIso (C := C) Y).hom.f 0 = f :=
      (congrArg₂ (· ≫ ·) e2 hUY).trans (Category.comp_id _)
    exact (c1.trans (a1.trans a2.symm)).trans c2.symm
  · have hX1 : ((CochainComplex.single₀ C).obj X).X n = (0 : C) := by
      simp [CochainComplex.single₀, HomologicalComplex.single, hn]
    have hZ : IsZero (((CochainComplex.single₀ C).obj X).X n) :=
      hX1.symm ▸ isZero_zero C
    exact hZ.eq_of_src _ _

/-- Let `C` be abelian and `I` an injective resolution of `S.X₃`.
Its augmentation followed by the inverse comparison to the transported
opposite projective complex equals the opposite projective augmentation
after the canonical degree-zero single-object comparison. -/
theorem augmentation_bridge_left (I : InjectiveResolution S.X₃) :
    I.ι ≫ (unopObjIsoL I).inv =
      (single₀UnopIso (C := C) S.X₃).hom ≫
        (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
          (opProjLeft I).π.op := by
  apply HomologicalComplex.Hom.ext
  funext n
  have b1 : ((I.ι ≫ (unopObjIsoL I).inv)).f n = I.ι.f n ≫ 𝟙 _ := rfl
  have b2 : (((single₀UnopIso (C := C) S.X₃).hom ≫
        (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
          (opProjLeft I).π.op)).f n =
      (single₀UnopIso (C := C) S.X₃).hom.f n ≫
        (((HomologicalComplex.opFunctor C (ComplexShape.up ℕ)).map I.ι.op).f n ≫
          (single₀OpIso S.X₃).hom.f n).unop := rfl
  have b3 : (((HomologicalComplex.opFunctor C (ComplexShape.up ℕ)).map I.ι.op).f n) =
      (I.ι.f n).op := rfl
  by_cases hn : n = 0
  · subst hn
    have hU0 : (single₀UnopIso (C := C) S.X₃).hom.f 0 = 𝟙 _ := rfl
    have hO0 : (single₀OpIso S.X₃).hom.f 0 =
        𝟙 (Opposite.op (((CochainComplex.single₀ C).obj S.X₃).X 0)) :=
      single₀OpIso_hom_f_zero S.X₃
    -- Freshly elaborated (uniform instances), so `simp` fires here even
    -- though it cannot inside the `rw`-produced goal below.
    have hinner : ((I.ι.f 0).op ≫
          𝟙 (Opposite.op (((CochainComplex.single₀ C).obj S.X₃).X 0))).unop =
        I.ι.f 0 := by
      simp only [Category.comp_id, Quiver.Hom.unop_op]
    rw [b1, b2, b3, hU0, hO0]
    exact (Category.comp_id _).trans ((Category.id_comp _).symm.trans
      (congrArg (𝟙 _ ≫ ·) hinner).symm)
  · have hX1 : ((CochainComplex.single₀ C).obj S.X₃).X n = (0 : C) := by
      simp [CochainComplex.single₀, HomologicalComplex.single, hn]
    have hZ : IsZero (((CochainComplex.single₀ C).obj S.X₃).X n) :=
      hX1.symm ▸ isZero_zero C
    exact hZ.eq_of_src _ _

end HorseshoeData

variable {S : ShortComplex C} {hS : S.ShortExact}
  {I₁ : InjectiveResolution S.X₁} {I₃ : InjectiveResolution S.X₃}

/- Proof implementation note.
The injective horseshoe from explicit endpoint resolutions.

Informal sketch: apply the projective horseshoe in `Cᵒᵖ`, unop the middle
resolution (`projectiveResolutionUnopInj`) and the SES maps (swapping
inclusion/projection since `unop` reverses arrows). Augmentation compatibilities
are the unop'd op-side ones; the proofs need `single₀`-naturality of
`single₀UnopIso` through `op` (`HorseshoeData.single₀UnopIso_naturality`).
-/

/-- For a short exact sequence `S : X₁ → X₂ → X₃` in an abelian category
`C`, and injective resolutions `I₁` of `X₁`, `I₃` of `X₃`, the horseshoe
construction supplies an injective resolution of `X₂`. Its resolution complex
fits into a short exact sequence `I₁ → middle → I₃`, and both maps commute
with the endpoint and middle augmentations. -/
noncomputable def horseshoe : HorseshoeData hS I₁ I₃ where
  middle := projectiveResolutionUnopInj
      (HorseshoeData.opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).middle
  i := HorseshoeData.horseshoeI (hS := hS) (I₁ := I₁) (I₃ := I₃)
  p := HorseshoeData.horseshoeP (hS := hS) (I₁ := I₁) (I₃ := I₃)
  zero := HorseshoeData.horseshoe_zero (hS := hS) (I₁ := I₁) (I₃ := I₃)
  shortExact := HorseshoeData.horseshoe_shortExact (hS := hS) (I₁ := I₁) (I₃ := I₃)
  i_augmentation := by
    have hi : HorseshoeData.horseshoeI (hS := hS) (I₁ := I₁) (I₃ := I₃) =
        (unopObjIsoR I₁).inv ≫
          (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
            (HorseshoeData.opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).p.op := rfl
    have hm : (projectiveResolutionUnopInj
          (HorseshoeData.opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).middle).ι =
        (single₀UnopIso _).hom ≫
          (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
            (HorseshoeData.opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).middle.π.op := rfl
    have hb := HorseshoeData.augmentation_bridge_right I₁
    have hop := (HorseshoeData.opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).p_augmentation
    have hnat : (single₀UnopIso (C := C) S.X₁).hom ≫
          (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
            (((ChainComplex.single₀ Cᵒᵖ).map S.op.g).op) =
        (CochainComplex.single₀ C).map S.f ≫
          (single₀UnopIso (C := C) S.X₂).hom :=
      HorseshoeData.single₀UnopIso_naturality S.f
    have s1 : I₁.ι ≫ HorseshoeData.horseshoeI (hS := hS) (I₁ := I₁) (I₃ := I₃) =
        (I₁.ι ≫ (unopObjIsoR I₁).inv) ≫
          (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
            (HorseshoeData.opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).p.op :=
      (congrArg (I₁.ι ≫ ·) hi).trans (Category.assoc _ _ _).symm
    have s2 : (I₁.ι ≫ (unopObjIsoR I₁).inv) ≫
          (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
            (HorseshoeData.opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).p.op =
        ((single₀UnopIso (C := C) S.X₁).hom ≫
            (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
              (opProjRight I₁).π.op) ≫
          (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
            (HorseshoeData.opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).p.op :=
      congrArg (· ≫ (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
        (HorseshoeData.opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).p.op) hb
    have s3 : ((single₀UnopIso (C := C) S.X₁).hom ≫
            (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
              (opProjRight I₁).π.op) ≫
          (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
            (HorseshoeData.opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).p.op =
        (single₀UnopIso (C := C) S.X₁).hom ≫
          (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
            ((opProjRight I₁).π.op ≫
              (HorseshoeData.opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).p.op) :=
      (Category.assoc _ _ _).trans
        (congrArg ((single₀UnopIso (C := C) S.X₁).hom ≫ ·)
          (Functor.map_comp _ _ _).symm)
    have s4 : (single₀UnopIso (C := C) S.X₁).hom ≫
          (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
            ((opProjRight I₁).π.op ≫
              (HorseshoeData.opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).p.op) =
        (single₀UnopIso (C := C) S.X₁).hom ≫
          (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
            ((HorseshoeData.opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).p ≫
              (opProjRight I₁).π).op :=
      congrArg ((single₀UnopIso (C := C) S.X₁).hom ≫
        (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map ·)
        op_comp.symm
    have s5 : (single₀UnopIso (C := C) S.X₁).hom ≫
          (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
            ((HorseshoeData.opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).p ≫
              (opProjRight I₁).π).op =
        (single₀UnopIso (C := C) S.X₁).hom ≫
          (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
            ((HorseshoeData.opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).middle.π ≫
              (ChainComplex.single₀ Cᵒᵖ).map S.op.g).op :=
      congrArg ((single₀UnopIso (C := C) S.X₁).hom ≫
        (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map ·)
        (congrArg Quiver.Hom.op hop)
    have s6 : (single₀UnopIso (C := C) S.X₁).hom ≫
          (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
            ((HorseshoeData.opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).middle.π ≫
              (ChainComplex.single₀ Cᵒᵖ).map S.op.g).op =
        (single₀UnopIso (C := C) S.X₁).hom ≫
          (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
            (((ChainComplex.single₀ Cᵒᵖ).map S.op.g).op ≫
              (HorseshoeData.opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).middle.π.op) :=
      congrArg ((single₀UnopIso (C := C) S.X₁).hom ≫
        (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map ·)
        op_comp
    have s7 : (single₀UnopIso (C := C) S.X₁).hom ≫
          (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
            (((ChainComplex.single₀ Cᵒᵖ).map S.op.g).op ≫
              (HorseshoeData.opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).middle.π.op) =
        ((single₀UnopIso (C := C) S.X₁).hom ≫
            (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
              (((ChainComplex.single₀ Cᵒᵖ).map S.op.g).op)) ≫
          (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
            (HorseshoeData.opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).middle.π.op :=
      (congrArg ((single₀UnopIso (C := C) S.X₁).hom ≫ ·)
        (Functor.map_comp _ _ _)).trans (Category.assoc _ _ _).symm
    have s8 : ((single₀UnopIso (C := C) S.X₁).hom ≫
            (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
              (((ChainComplex.single₀ Cᵒᵖ).map S.op.g).op)) ≫
          (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
            (HorseshoeData.opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).middle.π.op =
        (((CochainComplex.single₀ C).map S.f ≫
            (single₀UnopIso (C := C) S.X₂).hom) ≫
          (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
            (HorseshoeData.opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).middle.π.op) :=
      congrArg (· ≫ (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
        (HorseshoeData.opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).middle.π.op) hnat
    have s9 : (((CochainComplex.single₀ C).map S.f ≫
            (single₀UnopIso (C := C) S.X₂).hom) ≫
          (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
            (HorseshoeData.opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).middle.π.op) =
        (CochainComplex.single₀ C).map S.f ≫
          (projectiveResolutionUnopInj
            (HorseshoeData.opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).middle).ι :=
      (Category.assoc _ _ _).trans
        (congrArg ((CochainComplex.single₀ C).map S.f ≫ ·) hm.symm)
    exact s1.trans
      (s2.trans (s3.trans (s4.trans (s5.trans (s6.trans (s7.trans (s8.trans s9)))))))
  p_augmentation := by
    have hp : HorseshoeData.horseshoeP (hS := hS) (I₁ := I₁) (I₃ := I₃) =
        (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
            (HorseshoeData.opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).i.op ≫
          (unopObjIsoL I₃).hom := rfl
    have hm : (projectiveResolutionUnopInj
          (HorseshoeData.opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).middle).ι =
        (single₀UnopIso _).hom ≫
          (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
            (HorseshoeData.opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).middle.π.op := rfl
    have hhom : (unopObjIsoL I₃).hom = 𝟙 _ := rfl
    have hinv : (unopObjIsoL I₃).inv = 𝟙 _ := rfl
    have hp' : HorseshoeData.horseshoeP (hS := hS) (I₁ := I₁) (I₃ := I₃) =
        (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
          (HorseshoeData.opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).i.op :=
      hp.trans ((congrArg ((HomologicalComplex.unopFunctor C
        (ComplexShape.down ℕ)).map
        (HorseshoeData.opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).i.op ≫ ·) hhom).trans
        (Category.comp_id _))
    have hb := HorseshoeData.augmentation_bridge_left I₃
    have hop := (HorseshoeData.opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).i_augmentation
    have hnat : (single₀UnopIso ((S.op.X₂).unop)).hom ≫
          (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
            (((ChainComplex.single₀ Cᵒᵖ).map S.op.f).op) =
        (CochainComplex.single₀ C).map S.g ≫
          (single₀UnopIso (C := C) S.X₃).hom :=
      HorseshoeData.single₀UnopIso_naturality S.g
    have e9 : (single₀UnopIso (C := C) S.X₃).hom ≫
          (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
            (opProjLeft I₃).π.op = I₃.ι :=
      hb.symm.trans ((congrArg (I₃.ι ≫ ·) hinv).trans (Category.comp_id _))
    have t1 : (projectiveResolutionUnopInj
            (HorseshoeData.opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).middle).ι ≫
          HorseshoeData.horseshoeP (hS := hS) (I₁ := I₁) (I₃ := I₃) =
        ((single₀UnopIso ((S.op.X₂).unop)).hom ≫
            (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
              (HorseshoeData.opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).middle.π.op) ≫
          (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
            (HorseshoeData.opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).i.op :=
      congrArg₂ (· ≫ ·) hm hp'
    have t2 : ((single₀UnopIso ((S.op.X₂).unop)).hom ≫
            (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
              (HorseshoeData.opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).middle.π.op) ≫
          (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
            (HorseshoeData.opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).i.op =
        (single₀UnopIso ((S.op.X₂).unop)).hom ≫
          ((HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
              (HorseshoeData.opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).middle.π.op ≫
            (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
              (HorseshoeData.opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).i.op) :=
      Category.assoc _ _ _
    have t3 : (single₀UnopIso ((S.op.X₂).unop)).hom ≫
          ((HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
              (HorseshoeData.opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).middle.π.op ≫
            (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
              (HorseshoeData.opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).i.op) =
        (single₀UnopIso ((S.op.X₂).unop)).hom ≫
          (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
            ((HorseshoeData.opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).middle.π.op ≫
              (HorseshoeData.opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).i.op) :=
      congrArg ((single₀UnopIso ((S.op.X₂).unop)).hom ≫ ·)
        (Functor.map_comp _ _ _).symm
    have t4 : (single₀UnopIso ((S.op.X₂).unop)).hom ≫
          (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
            ((HorseshoeData.opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).middle.π.op ≫
              (HorseshoeData.opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).i.op) =
        (single₀UnopIso ((S.op.X₂).unop)).hom ≫
          (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
            ((HorseshoeData.opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).i ≫
              (HorseshoeData.opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).middle.π).op :=
      congrArg ((single₀UnopIso ((S.op.X₂).unop)).hom ≫
        (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map ·)
        op_comp.symm
    have t5 : (single₀UnopIso ((S.op.X₂).unop)).hom ≫
          (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
            ((HorseshoeData.opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).i ≫
              (HorseshoeData.opHorseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).middle.π).op =
        (single₀UnopIso ((S.op.X₂).unop)).hom ≫
          (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
            ((opProjLeft I₃).π ≫
              (ChainComplex.single₀ Cᵒᵖ).map S.op.f).op :=
      congrArg ((single₀UnopIso ((S.op.X₂).unop)).hom ≫
        (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map ·)
        (congrArg Quiver.Hom.op hop)
    have t6 : (single₀UnopIso ((S.op.X₂).unop)).hom ≫
          (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
            ((opProjLeft I₃).π ≫
              (ChainComplex.single₀ Cᵒᵖ).map S.op.f).op =
        (single₀UnopIso ((S.op.X₂).unop)).hom ≫
          (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
            (((ChainComplex.single₀ Cᵒᵖ).map S.op.f).op ≫
              (opProjLeft I₃).π.op) :=
      congrArg ((single₀UnopIso ((S.op.X₂).unop)).hom ≫
        (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map ·)
        op_comp
    have t7 : (single₀UnopIso ((S.op.X₂).unop)).hom ≫
          (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
            (((ChainComplex.single₀ Cᵒᵖ).map S.op.f).op ≫
              (opProjLeft I₃).π.op) =
        ((single₀UnopIso ((S.op.X₂).unop)).hom ≫
            (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
              (((ChainComplex.single₀ Cᵒᵖ).map S.op.f).op)) ≫
          (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
            (opProjLeft I₃).π.op :=
      (congrArg ((single₀UnopIso ((S.op.X₂).unop)).hom ≫ ·)
        (Functor.map_comp _ _ _)).trans (Category.assoc _ _ _).symm
    have t8 : ((single₀UnopIso ((S.op.X₂).unop)).hom ≫
            (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
              (((ChainComplex.single₀ Cᵒᵖ).map S.op.f).op)) ≫
          (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
            (opProjLeft I₃).π.op =
        (((CochainComplex.single₀ C).map S.g ≫
            (single₀UnopIso (C := C) S.X₃).hom) ≫
          (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
            (opProjLeft I₃).π.op) :=
      congrArg (· ≫ (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
        (opProjLeft I₃).π.op) hnat
    have t9 : (((CochainComplex.single₀ C).map S.g ≫
            (single₀UnopIso (C := C) S.X₃).hom) ≫
          (HomologicalComplex.unopFunctor C (ComplexShape.down ℕ)).map
            (opProjLeft I₃).π.op) =
        (CochainComplex.single₀ C).map S.g ≫ I₃.ι :=
      (Category.assoc _ _ _).trans
        (congrArg ((CochainComplex.single₀ C).map S.g ≫ ·) e9)
    exact t1.trans
      (t2.trans (t3.trans (t4.trans (t5.trans (t6.trans (t7.trans (t8.trans t9)))))))

namespace HorseshoeData

/-- For horseshoe data `H` over a short exact sequence `S` in an abelian
category `C` and injective endpoints `I₁`, `I₃`, a coordinate specification
chooses `Hⁿ ≅ I₁ⁿ ⊞ I₃ⁿ` in each degree. The inclusion and projection are
the biproduct maps, and the degree `n → n + 1` differential has matrix
`[[d₁, κ], [0, d₃]]`. -/
structure Spec (H : HorseshoeData hS I₁ I₃) where
  /-- For a coordinate specification of horseshoe data `H` in an abelian
category `C`, the middle resolution object in degree `n : ℕ` is isomorphic
to the biproduct `I₁.cocomplex.X n ⊞ I₃.cocomplex.X n` of the endpoint terms. -/
  middleXIso (n : ℕ) : H.middle.cocomplex.X n ≅
    I₁.cocomplex.X n ⊞ I₃.cocomplex.X n
  /-- For horseshoe data `H` in an abelian category `C` with a chosen degreewise
biproduct specification, the degree-`n` inclusion of `I₁` followed by the
middle coordinate isomorphism is `biprod.inl : I₁ⁿ → I₁ⁿ ⊞ I₃ⁿ`. -/
  i_f (n : ℕ) : H.i.f n ≫ (middleXIso n).hom = biprod.inl
  /-- For horseshoe data `H` in an abelian category `C` with a chosen degreewise
biproduct specification, the inverse middle coordinate isomorphism followed
by the degree-`n` projection onto `I₃` is `biprod.snd : I₁ⁿ ⊞ I₃ⁿ → I₃ⁿ`. -/
  p_f (n : ℕ) : (middleXIso n).inv ≫ H.p.f n = biprod.snd
  /-- For a coordinate specification of horseshoe data `H` in an abelian category
`C`, conjugating its differential `Hⁿ → Hⁿ⁺¹` by the chosen biproduct
isomorphisms gives `[[d₁, κ], [0, d₃]]`. Here `d₁`, `d₃` are the endpoint
cochain differentials and `κ : I₃ⁿ → I₁ⁿ⁺¹` is the remaining corner of the
middle differential. -/
  middle_d (n : ℕ) :
    (middleXIso n).inv ≫ H.middle.cocomplex.d n (n + 1) ≫
        (middleXIso (n + 1)).hom =
      Biprod.ofComponents (I₁.cocomplex.d n (n + 1)) 0
        (biprod.inr ≫
          ((middleXIso n).inv ≫ H.middle.cocomplex.d n (n + 1) ≫
            (middleXIso (n + 1)).hom) ≫ biprod.fst)
        (I₃.cocomplex.d n (n + 1))

end HorseshoeData

/- Proof implementation note.
The middle object iso: unop of the projective coordinates, `unop` pushed
through the biproduct, then swapped into `(I₁ ⊞ I₃)` order.

Informal sketch: `(H.middle.complex.X n).unop ≅ unop (op I₃.X n ⊞ op I₁.X n)`
(unop'd `ProjectiveResolution.horseshoe_middle_X_iso`) `≅ unop (op I₃.X n) ⊞ unop (op I₁.X n)`
(`unopBiprodIso`) `= I₃.X n ⊞ I₁.X n` (definitionally) `≅ I₁.X n ⊞ I₃.X n`
(`biprod.braiding'`).
-/

/-- For a short exact sequence `S` in an abelian category `C` and endpoint
injective resolutions `I₁`, `I₃`, the horseshoe middle term in degree `n`
is canonically isomorphic to `I₁.cocomplex.X n ⊞ I₃.cocomplex.X n`.
These coordinates are obtained from the opposite projective horseshoe and
put the endpoint factors in `I₁`, `I₃` order. -/
noncomputable def horseshoeMiddleXIso (n : ℕ) :
    (horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).middle.cocomplex.X n ≅
      I₁.cocomplex.X n ⊞ I₃.cocomplex.X n :=
  (ProjectiveResolution.horseshoe_middle_X_iso hS.op
    (opProjLeft I₃) (opProjRight I₁) n).unop.symm ≪≫
    unopBiprodIso ≪≫
    biprod.braiding' (I₃.cocomplex.X n) (I₁.cocomplex.X n)

/-- For the injective horseshoe of a short exact sequence `S` in an abelian
category `C`, with endpoint resolutions `I₁`, `I₃`, its degree-`n` inclusion
followed by `horseshoeMiddleXIso n` is the left biproduct inclusion
`I₁ⁿ → I₁ⁿ ⊞ I₃ⁿ`. -/
@[simp]
theorem horseshoe_i_f (n : ℕ) :
    (horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).i.f n ≫
      (horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) n).hom = biprod.inl := by
    have hIf : (horseshoe (hS := hS) (I₁ := I₁)
          (I₃ := I₃)).i.f n =
        𝟙 _ ≫ ((ProjectiveResolution.horseshoe hS.op (opProjLeft I₃)
          (opProjRight I₁)).p.f n).unop := rfl
    have hM : (horseshoeMiddleXIso (hS := hS) (I₁ := I₁)
          (I₃ := I₃) n).hom =
        (ProjectiveResolution.horseshoe_middle_X_iso hS.op
              (opProjLeft I₃) (opProjRight I₁) n).inv.unop ≫
          (biprod.lift (biprod.inl : (opProjLeft I₃).complex.X n ⟶
              (opProjLeft I₃).complex.X n ⊞ (opProjRight I₁).complex.X n).unop
              (biprod.inr : (opProjRight I₁).complex.X n ⟶
              (opProjLeft I₃).complex.X n ⊞ (opProjRight I₁).complex.X n).unop ≫
            (biprod.braiding' (I₃.cocomplex.X n)
              (I₁.cocomplex.X n)).hom) := rfl
    have hLift : (biprod.snd : (opProjLeft I₃).complex.X n ⊞
            (opProjRight I₁).complex.X n ⟶
            (opProjRight I₁).complex.X n).unop ≫
          biprod.lift (biprod.inl : (opProjLeft I₃).complex.X n ⟶
              (opProjLeft I₃).complex.X n ⊞ (opProjRight I₁).complex.X n).unop
              (biprod.inr : (opProjRight I₁).complex.X n ⟶
              (opProjLeft I₃).complex.X n ⊞ (opProjRight I₁).complex.X n).unop =
          (biprod.inr : ((opProjRight I₁).complex.X n).unop ⟶
            ((opProjLeft I₃).complex.X n).unop ⊞
              ((opProjRight I₁).complex.X n).unop) := by
      apply biprod.hom_ext
      · rw [Category.assoc, biprod.lift_fst, ← unop_comp, biprod.inl_snd,
          unop_zero, biprod.inr_fst]
      · rw [Category.assoc, biprod.lift_snd, ← unop_comp, biprod.inr_snd,
          unop_id, biprod.inr_snd]
    have hpf := ProjectiveResolution.horseshoe_p_f hS.op (opProjLeft I₃)
      (opProjRight I₁) n
    rw [hIf, hM]
    -- Have-chain (not `calc`): the final join crosses a default-only defeq
    -- (`((opProjRight I₁).complex.X n).unop ≡ I₁.cocomplex.X n`), which
    -- `calc`'s `Trans` cannot see.
    have c1 : (𝟙 _ ≫ ((ProjectiveResolution.horseshoe hS.op (opProjLeft I₃)
              (opProjRight I₁)).p.f n).unop) ≫
            ((ProjectiveResolution.horseshoe_middle_X_iso hS.op
                (opProjLeft I₃) (opProjRight I₁) n).inv.unop ≫
              (biprod.lift (biprod.inl : (opProjLeft I₃).complex.X n ⟶
                  (opProjLeft I₃).complex.X n ⊞ (opProjRight I₁).complex.X n).unop
                  (biprod.inr : (opProjRight I₁).complex.X n ⟶
                  (opProjLeft I₃).complex.X n ⊞ (opProjRight I₁).complex.X n).unop ≫
              (biprod.braiding' (I₃.cocomplex.X n)
                (I₁.cocomplex.X n)).hom))
          = ((ProjectiveResolution.horseshoe hS.op (opProjLeft I₃)
              (opProjRight I₁)).p.f n).unop ≫
            ((ProjectiveResolution.horseshoe_middle_X_iso hS.op
                (opProjLeft I₃) (opProjRight I₁) n).inv.unop ≫
              (biprod.lift (biprod.inl : (opProjLeft I₃).complex.X n ⟶
                  (opProjLeft I₃).complex.X n ⊞ (opProjRight I₁).complex.X n).unop
                  (biprod.inr : (opProjRight I₁).complex.X n ⟶
                  (opProjLeft I₃).complex.X n ⊞ (opProjRight I₁).complex.X n).unop ≫
              (biprod.braiding' (I₃.cocomplex.X n)
                (I₁.cocomplex.X n)).hom)) := by
      simp only [Category.id_comp]
    have c2 : (((ProjectiveResolution.horseshoe hS.op (opProjLeft I₃)
              (opProjRight I₁)).p.f n).unop ≫
            ((ProjectiveResolution.horseshoe_middle_X_iso hS.op
                (opProjLeft I₃) (opProjRight I₁) n).inv.unop ≫
              (biprod.lift (biprod.inl : (opProjLeft I₃).complex.X n ⟶
                  (opProjLeft I₃).complex.X n ⊞ (opProjRight I₁).complex.X n).unop
                  (biprod.inr : (opProjRight I₁).complex.X n ⟶
                  (opProjLeft I₃).complex.X n ⊞ (opProjRight I₁).complex.X n).unop ≫
              (biprod.braiding' (I₃.cocomplex.X n)
                (I₁.cocomplex.X n)).hom)))
          = ((((ProjectiveResolution.horseshoe hS.op (opProjLeft I₃)
              (opProjRight I₁)).p.f n).unop ≫
            (ProjectiveResolution.horseshoe_middle_X_iso hS.op
              (opProjLeft I₃) (opProjRight I₁) n).inv.unop) ≫
            biprod.lift (biprod.inl : (opProjLeft I₃).complex.X n ⟶
                (opProjLeft I₃).complex.X n ⊞ (opProjRight I₁).complex.X n).unop
                (biprod.inr : (opProjRight I₁).complex.X n ⟶
                (opProjLeft I₃).complex.X n ⊞ (opProjRight I₁).complex.X n).unop) ≫
            (biprod.braiding' (I₃.cocomplex.X n)
              (I₁.cocomplex.X n)).hom :=
      (Category.assoc _ _ _).symm.trans (Category.assoc _ _ _).symm
    have c3 : ((((ProjectiveResolution.horseshoe hS.op (opProjLeft I₃)
              (opProjRight I₁)).p.f n).unop ≫
            (ProjectiveResolution.horseshoe_middle_X_iso hS.op
              (opProjLeft I₃) (opProjRight I₁) n).inv.unop) ≫
            biprod.lift (biprod.inl : (opProjLeft I₃).complex.X n ⟶
                (opProjLeft I₃).complex.X n ⊞ (opProjRight I₁).complex.X n).unop
                (biprod.inr : (opProjRight I₁).complex.X n ⟶
                (opProjLeft I₃).complex.X n ⊞ (opProjRight I₁).complex.X n).unop) ≫
            (biprod.braiding' (I₃.cocomplex.X n)
              (I₁.cocomplex.X n)).hom
          = ((biprod.snd : (opProjLeft I₃).complex.X n ⊞
              (opProjRight I₁).complex.X n ⟶
              (opProjRight I₁).complex.X n).unop ≫
            biprod.lift (biprod.inl : (opProjLeft I₃).complex.X n ⟶
                (opProjLeft I₃).complex.X n ⊞ (opProjRight I₁).complex.X n).unop
                (biprod.inr : (opProjRight I₁).complex.X n ⟶
                (opProjLeft I₃).complex.X n ⊞ (opProjRight I₁).complex.X n).unop) ≫
            (biprod.braiding' (I₃.cocomplex.X n)
              (I₁.cocomplex.X n)).hom := by
      rw [← unop_comp, hpf]
    have c4 : (((biprod.snd : (opProjLeft I₃).complex.X n ⊞
              (opProjRight I₁).complex.X n ⟶
              (opProjRight I₁).complex.X n).unop ≫
            biprod.lift (biprod.inl : (opProjLeft I₃).complex.X n ⟶
                (opProjLeft I₃).complex.X n ⊞ (opProjRight I₁).complex.X n).unop
                (biprod.inr : (opProjRight I₁).complex.X n ⟶
                (opProjLeft I₃).complex.X n ⊞ (opProjRight I₁).complex.X n).unop) ≫
            (biprod.braiding' (I₃.cocomplex.X n)
              (I₁.cocomplex.X n)).hom) = biprod.inl := by
      rw [hLift]
      -- Normalize across the defeq boundary (`inr` is `rfl`-defeq on
      -- defeq objects, so `inr_desc` matches syntactically after this).
      change (biprod.inr : I₁.cocomplex.X n ⟶
          I₃.cocomplex.X n ⊞ I₁.cocomplex.X n) ≫
        biprod.desc (biprod.inr : I₃.cocomplex.X n ⟶
          I₁.cocomplex.X n ⊞ I₃.cocomplex.X n)
          (biprod.inl : I₁.cocomplex.X n ⟶
            I₁.cocomplex.X n ⊞ I₃.cocomplex.X n) = biprod.inl
      rw [biprod.inr_desc]
    exact c1.trans (c2.trans (c3.trans c4))

/-- For the injective horseshoe of a short exact sequence `S` in an abelian
category `C`, with endpoint resolutions `I₁`, `I₃`, the inverse of
`horseshoeMiddleXIso n` followed by its degree-`n` projection is the right
biproduct projection `I₁ⁿ ⊞ I₃ⁿ → I₃ⁿ`. -/
@[simp]
theorem horseshoe_p_f (n : ℕ) :
    (horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) n).inv ≫
      (horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).p.f n = biprod.snd := by
    have hPf : (horseshoe (hS := hS) (I₁ := I₁)
          (I₃ := I₃)).p.f n =
        ((ProjectiveResolution.horseshoe hS.op (opProjLeft I₃)
          (opProjRight I₁)).i.f n).unop ≫ 𝟙 _ := rfl
    have hMInv : (horseshoeMiddleXIso (hS := hS) (I₁ := I₁)
          (I₃ := I₃) n).inv =
        ((biprod.braiding' (I₃.cocomplex.X n)
            (I₁.cocomplex.X n)).inv ≫
          (biprod.desc (biprod.fst : (opProjLeft I₃).complex.X n ⊞
              (opProjRight I₁).complex.X n ⟶ (opProjLeft I₃).complex.X n).unop
              (biprod.snd : (opProjLeft I₃).complex.X n ⊞ (opProjRight I₁).complex.X n ⟶
              (opProjRight I₁).complex.X n).unop :
              ((opProjLeft I₃).complex.X n).unop ⊞ ((opProjRight I₁).complex.X n).unop ⟶
              ((opProjLeft I₃).complex.X n ⊞ (opProjRight I₁).complex.X n).unop)) ≫
          (ProjectiveResolution.horseshoe_middle_X_iso hS.op
            (opProjLeft I₃) (opProjRight I₁) n).hom.unop := rfl
    have hDesc : (biprod.desc (biprod.fst : (opProjLeft I₃).complex.X n ⊞
        (opProjRight I₁).complex.X n ⟶ (opProjLeft I₃).complex.X n).unop
        (biprod.snd : (opProjLeft I₃).complex.X n ⊞ (opProjRight I₁).complex.X n ⟶
        (opProjRight I₁).complex.X n).unop :
        ((opProjLeft I₃).complex.X n).unop ⊞ ((opProjRight I₁).complex.X n).unop ⟶
        ((opProjLeft I₃).complex.X n ⊞ (opProjRight I₁).complex.X n).unop) ≫
        (biprod.inl : (opProjLeft I₃).complex.X n ⟶
          (opProjLeft I₃).complex.X n ⊞
          (opProjRight I₁).complex.X n).unop =
        (biprod.fst : ((opProjLeft I₃).complex.X n).unop ⊞
          ((opProjRight I₁).complex.X n).unop ⟶
          ((opProjLeft I₃).complex.X n).unop) := by
      apply biprod.hom_ext'
      · rw [← Category.assoc, biprod.inl_desc, ← unop_comp, biprod.inl_fst,
          unop_id, biprod.inl_fst]
      · rw [← Category.assoc, biprod.inr_desc, ← unop_comp, biprod.inl_snd,
          unop_zero, biprod.inr_fst]
    have hif := ProjectiveResolution.horseshoe_i_f hS.op (opProjLeft I₃)
      (opProjRight I₁) n
    rw [hPf, hMInv]
    have d1 : (((biprod.braiding' (I₃.cocomplex.X n)
              (I₁.cocomplex.X n)).inv ≫
            (biprod.desc (biprod.fst : (opProjLeft I₃).complex.X n ⊞
                (opProjRight I₁).complex.X n ⟶ (opProjLeft I₃).complex.X n).unop
                (biprod.snd : (opProjLeft I₃).complex.X n ⊞ (opProjRight I₁).complex.X n ⟶
                (opProjRight I₁).complex.X n).unop :
                ((opProjLeft I₃).complex.X n).unop ⊞ ((opProjRight I₁).complex.X n).unop ⟶
                ((opProjLeft I₃).complex.X n ⊞ (opProjRight I₁).complex.X n).unop)) ≫
            (ProjectiveResolution.horseshoe_middle_X_iso hS.op
              (opProjLeft I₃) (opProjRight I₁) n).hom.unop) ≫
          (((ProjectiveResolution.horseshoe hS.op (opProjLeft I₃)
            (opProjRight I₁)).i.f n).unop ≫ 𝟙 _)
          = (((biprod.braiding' (I₃.cocomplex.X n)
              (I₁.cocomplex.X n)).inv ≫
            (biprod.desc (biprod.fst : (opProjLeft I₃).complex.X n ⊞
                (opProjRight I₁).complex.X n ⟶ (opProjLeft I₃).complex.X n).unop
                (biprod.snd : (opProjLeft I₃).complex.X n ⊞ (opProjRight I₁).complex.X n ⟶
                (opProjRight I₁).complex.X n).unop :
                ((opProjLeft I₃).complex.X n).unop ⊞ ((opProjRight I₁).complex.X n).unop ⟶
                ((opProjLeft I₃).complex.X n ⊞ (opProjRight I₁).complex.X n).unop)) ≫
            (ProjectiveResolution.horseshoe_middle_X_iso hS.op
              (opProjLeft I₃) (opProjRight I₁) n).hom.unop) ≫
          ((ProjectiveResolution.horseshoe hS.op (opProjLeft I₃)
            (opProjRight I₁)).i.f n).unop := by
      simp only [Category.comp_id]
    have d2 : (((biprod.braiding' (I₃.cocomplex.X n)
              (I₁.cocomplex.X n)).inv ≫
            (biprod.desc (biprod.fst : (opProjLeft I₃).complex.X n ⊞
                (opProjRight I₁).complex.X n ⟶ (opProjLeft I₃).complex.X n).unop
                (biprod.snd : (opProjLeft I₃).complex.X n ⊞ (opProjRight I₁).complex.X n ⟶
                (opProjRight I₁).complex.X n).unop :
                ((opProjLeft I₃).complex.X n).unop ⊞ ((opProjRight I₁).complex.X n).unop ⟶
                ((opProjLeft I₃).complex.X n ⊞ (opProjRight I₁).complex.X n).unop)) ≫
            (ProjectiveResolution.horseshoe_middle_X_iso hS.op
              (opProjLeft I₃) (opProjRight I₁) n).hom.unop) ≫
          ((ProjectiveResolution.horseshoe hS.op (opProjLeft I₃)
            (opProjRight I₁)).i.f n).unop
          = (biprod.braiding' (I₃.cocomplex.X n)
              (I₁.cocomplex.X n)).inv ≫
            ((biprod.desc (biprod.fst : (opProjLeft I₃).complex.X n ⊞
                (opProjRight I₁).complex.X n ⟶ (opProjLeft I₃).complex.X n).unop
                (biprod.snd : (opProjLeft I₃).complex.X n ⊞ (opProjRight I₁).complex.X n ⟶
                (opProjRight I₁).complex.X n).unop :
                ((opProjLeft I₃).complex.X n).unop ⊞ ((opProjRight I₁).complex.X n).unop ⟶
                ((opProjLeft I₃).complex.X n ⊞ (opProjRight I₁).complex.X n).unop) ≫
              ((ProjectiveResolution.horseshoe_middle_X_iso hS.op
                (opProjLeft I₃) (opProjRight I₁) n).hom.unop ≫
                ((ProjectiveResolution.horseshoe hS.op (opProjLeft I₃)
                  (opProjRight I₁)).i.f n).unop)) :=
      (Category.assoc _ _ _).trans (Category.assoc _ _ _)
    have d3 : ((biprod.braiding' (I₃.cocomplex.X n)
              (I₁.cocomplex.X n)).inv ≫
            ((biprod.desc (biprod.fst : (opProjLeft I₃).complex.X n ⊞
                (opProjRight I₁).complex.X n ⟶ (opProjLeft I₃).complex.X n).unop
                (biprod.snd : (opProjLeft I₃).complex.X n ⊞ (opProjRight I₁).complex.X n ⟶
                (opProjRight I₁).complex.X n).unop :
                ((opProjLeft I₃).complex.X n).unop ⊞ ((opProjRight I₁).complex.X n).unop ⟶
                ((opProjLeft I₃).complex.X n ⊞ (opProjRight I₁).complex.X n).unop) ≫
              ((ProjectiveResolution.horseshoe_middle_X_iso hS.op
                (opProjLeft I₃) (opProjRight I₁) n).hom.unop ≫
                ((ProjectiveResolution.horseshoe hS.op (opProjLeft I₃)
                  (opProjRight I₁)).i.f n).unop)))
          = (biprod.braiding' (I₃.cocomplex.X n)
              (I₁.cocomplex.X n)).inv ≫
            ((biprod.desc (biprod.fst : (opProjLeft I₃).complex.X n ⊞
                (opProjRight I₁).complex.X n ⟶ (opProjLeft I₃).complex.X n).unop
                (biprod.snd : (opProjLeft I₃).complex.X n ⊞ (opProjRight I₁).complex.X n ⟶
                (opProjRight I₁).complex.X n).unop :
                ((opProjLeft I₃).complex.X n).unop ⊞ ((opProjRight I₁).complex.X n).unop ⟶
                ((opProjLeft I₃).complex.X n ⊞ (opProjRight I₁).complex.X n).unop) ≫
              (biprod.inl : (opProjLeft I₃).complex.X n ⟶
                (opProjLeft I₃).complex.X n ⊞
                (opProjRight I₁).complex.X n).unop) := by
      rw [← unop_comp, hif]
    -- The swap step, kept in defeq-clean normal form (term-mode bridge
    -- below avoids rewriting across the defeq boundary).
    have hSwapStep : (biprod.braiding' (I₃.cocomplex.X n)
              (I₁.cocomplex.X n)).inv ≫
          (biprod.fst : ((opProjLeft I₃).complex.X n).unop ⊞
            ((opProjRight I₁).complex.X n).unop ⟶
            ((opProjLeft I₃).complex.X n).unop) = biprod.snd := by
      -- Normalize across the defeq boundary (`fst` is `rfl`-defeq on
      -- defeq objects, so the biproduct lemmas match syntactically).
      change (biprod.braiding' (I₃.cocomplex.X n)
          (I₁.cocomplex.X n)).inv ≫
        (biprod.fst : I₃.cocomplex.X n ⊞ I₁.cocomplex.X n ⟶
          I₃.cocomplex.X n) = biprod.snd
      have h1 : (biprod.inl : I₁.cocomplex.X n ⟶
            I₁.cocomplex.X n ⊞ I₃.cocomplex.X n) ≫
          (biprod.braiding' (I₃.cocomplex.X n)
            (I₁.cocomplex.X n)).inv =
          (biprod.inr : I₁.cocomplex.X n ⟶
            I₃.cocomplex.X n ⊞ I₁.cocomplex.X n) := by
        change (biprod.inl : I₁.cocomplex.X n ⟶
            I₁.cocomplex.X n ⊞ I₃.cocomplex.X n) ≫
          biprod.desc (biprod.inr : I₁.cocomplex.X n ⟶
            I₃.cocomplex.X n ⊞ I₁.cocomplex.X n)
            (biprod.inl : I₃.cocomplex.X n ⟶
              I₃.cocomplex.X n ⊞ I₁.cocomplex.X n) = _
        rw [biprod.inl_desc]
      have h2 : (biprod.inr : I₃.cocomplex.X n ⟶
            I₁.cocomplex.X n ⊞ I₃.cocomplex.X n) ≫
          (biprod.braiding' (I₃.cocomplex.X n)
            (I₁.cocomplex.X n)).inv =
          (biprod.inl : I₃.cocomplex.X n ⟶
            I₃.cocomplex.X n ⊞ I₁.cocomplex.X n) := by
        change (biprod.inr : I₃.cocomplex.X n ⟶
            I₁.cocomplex.X n ⊞ I₃.cocomplex.X n) ≫
          biprod.desc (biprod.inr : I₁.cocomplex.X n ⟶
            I₃.cocomplex.X n ⊞ I₁.cocomplex.X n)
            (biprod.inl : I₃.cocomplex.X n ⟶
              I₃.cocomplex.X n ⊞ I₁.cocomplex.X n) = _
        rw [biprod.inr_desc]
      apply biprod.hom_ext'
      · rw [← Category.assoc, h1, biprod.inr_fst, biprod.inl_snd]
      · rw [← Category.assoc, h2, biprod.inl_fst, biprod.inr_snd]
    have d4 : ((biprod.braiding' (I₃.cocomplex.X n)
              (I₁.cocomplex.X n)).inv ≫
            ((biprod.desc (biprod.fst : (opProjLeft I₃).complex.X n ⊞
                (opProjRight I₁).complex.X n ⟶ (opProjLeft I₃).complex.X n).unop
                (biprod.snd : (opProjLeft I₃).complex.X n ⊞ (opProjRight I₁).complex.X n ⟶
                (opProjRight I₁).complex.X n).unop :
                ((opProjLeft I₃).complex.X n).unop ⊞ ((opProjRight I₁).complex.X n).unop ⟶
                ((opProjLeft I₃).complex.X n ⊞ (opProjRight I₁).complex.X n).unop) ≫
              (biprod.inl : (opProjLeft I₃).complex.X n ⟶
                (opProjLeft I₃).complex.X n ⊞
                (opProjRight I₁).complex.X n).unop)) = biprod.snd :=
      (congrArg ((biprod.braiding' (I₃.cocomplex.X n)
        (I₁.cocomplex.X n)).inv ≫ ·) hDesc).trans hSwapStep
    exact d1.trans (d2.trans (d3.trans d4))

/-- For a short exact sequence `S` in an abelian category `C` and endpoint
injective resolutions `I₁`, `I₃`, the constructed injective horseshoe has
its canonical degreewise biproduct specification. Its differential has
matrix `[[d₁, κ], [0, d₃]]` and its resolution maps are the corresponding
biproduct inclusion and projection. -/
noncomputable def horseshoeSpec :
    (horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).Spec where
  middleXIso := horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃)
  i_f := horseshoe_i_f (hS := hS) (I₁ := I₁) (I₃ := I₃)
  p_f := horseshoe_p_f (hS := hS) (I₁ := I₁) (I₃ := I₃)
  middle_d := by
    intro n
    have hifn := horseshoe_i_f (hS := hS) (I₁ := I₁) (I₃ := I₃) n
    have hifS := horseshoe_i_f (hS := hS) (I₁ := I₁) (I₃ := I₃) (n + 1)
    have hpfn := horseshoe_p_f (hS := hS) (I₁ := I₁) (I₃ := I₃) n
    have hpfS := horseshoe_p_f (hS := hS) (I₁ := I₁) (I₃ := I₃) (n + 1)
    have hci := HomologicalComplex.Hom.comm
      (horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).i n (n + 1)
    have hcp := HomologicalComplex.Hom.comm
      (horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).p n (n + 1)
    -- k1 : inl ≫ φn.inv = H.i.f n
    have k1a : biprod.inl ≫ (horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) n).inv =
        ((horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).i.f n ≫
          (horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) n).hom) ≫
        (horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) n).inv :=
      congrArg (· ≫ (horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) n).inv)
        hifn.symm
    have k1b : ((horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).i.f n ≫
          (horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) n).hom) ≫
        (horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) n).inv =
        (horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).i.f n ≫
          ((horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) n).hom ≫
            (horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) n).inv) :=
      Category.assoc _ _ _
    have k1c : (horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).i.f n ≫
          ((horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) n).hom ≫
            (horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) n).inv) =
        (horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).i.f n ≫ 𝟙 _ :=
      congrArg ((horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).i.f n ≫ ·)
        (horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) n).hom_inv_id
    have k1d : (horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).i.f n ≫ 𝟙 _ =
        (horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).i.f n :=
      Category.comp_id _
    have k1 : biprod.inl ≫ (horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) n).inv =
        (horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).i.f n :=
      k1a.trans (k1b.trans (k1c.trans k1d))
    -- eBase : inl ≫ D = d1 ≫ (H.i.f (n+1) ≫ φS.hom)
    have b1 : biprod.inl ≫ ((horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) n).inv ≫
          (horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).middle.cocomplex.d n (n + 1) ≫
            (horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) (n + 1)).hom) =
        (biprod.inl ≫ (horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) n).inv) ≫
          ((horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).middle.cocomplex.d n (n + 1) ≫
            (horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) (n + 1)).hom) :=
      (Category.assoc _ _ _).symm
    have b2 : (biprod.inl ≫ (horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) n).inv) ≫
          ((horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).middle.cocomplex.d n (n + 1) ≫
            (horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) (n + 1)).hom) =
        (horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).i.f n ≫
          ((horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).middle.cocomplex.d n (n + 1) ≫
            (horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) (n + 1)).hom) :=
      congrArg (· ≫ ((horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).middle.cocomplex.d n (n + 1) ≫
        (horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) (n + 1)).hom)) k1
    have b3 : (horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).i.f n ≫
          ((horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).middle.cocomplex.d n (n + 1) ≫
            (horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) (n + 1)).hom) =
        ((horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).i.f n ≫
            (horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).middle.cocomplex.d n (n + 1)) ≫
          (horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) (n + 1)).hom :=
      (Category.assoc _ _ _).symm
    have b4 : ((horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).i.f n ≫
            (horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).middle.cocomplex.d n (n + 1)) ≫
          (horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) (n + 1)).hom =
        (I₁.cocomplex.d n (n + 1) ≫
            (horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).i.f (n + 1)) ≫
          (horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) (n + 1)).hom :=
      congrArg (· ≫ (horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) (n + 1)).hom)
        hci
    have b5 : (I₁.cocomplex.d n (n + 1) ≫
            (horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).i.f (n + 1)) ≫
          (horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) (n + 1)).hom =
        I₁.cocomplex.d n (n + 1) ≫
          ((horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).i.f (n + 1) ≫
            (horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) (n + 1)).hom) :=
      Category.assoc _ _ _
    have eBase : biprod.inl ≫ ((horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) n).inv ≫
          (horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).middle.cocomplex.d n (n + 1) ≫
            (horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) (n + 1)).hom) =
        I₁.cocomplex.d n (n + 1) ≫
          ((horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).i.f (n + 1) ≫
            (horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) (n + 1)).hom) :=
      b1.trans (b2.trans (b3.trans (b4.trans b5)))
    -- e11 : (inl ≫ D) ≫ fst = d1
    have c0 : biprod.inl ≫ ((horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) n).inv ≫
          (horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).middle.cocomplex.d n (n + 1) ≫
            (horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) (n + 1)).hom) ≫
          biprod.fst =
        (biprod.inl ≫ ((horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) n).inv ≫
            (horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).middle.cocomplex.d n (n + 1) ≫
              (horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) (n + 1)).hom)) ≫
          biprod.fst :=
      (Category.assoc _ _ _).symm
    have c1 : (biprod.inl ≫ ((horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) n).inv ≫
            (horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).middle.cocomplex.d n (n + 1) ≫
              (horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) (n + 1)).hom)) ≫
          biprod.fst =
        (I₁.cocomplex.d n (n + 1) ≫
            ((horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).i.f (n + 1) ≫
              (horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) (n + 1)).hom)) ≫
          biprod.fst :=
      congrArg (· ≫ biprod.fst) eBase
    have c2 : (I₁.cocomplex.d n (n + 1) ≫
            ((horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).i.f (n + 1) ≫
              (horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) (n + 1)).hom)) ≫
          biprod.fst =
        I₁.cocomplex.d n (n + 1) ≫
          (((horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).i.f (n + 1) ≫
              (horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) (n + 1)).hom) ≫
            biprod.fst) :=
      Category.assoc _ _ _
    have c3 : I₁.cocomplex.d n (n + 1) ≫
          (((horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).i.f (n + 1) ≫
              (horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) (n + 1)).hom) ≫
            biprod.fst) =
        I₁.cocomplex.d n (n + 1) ≫
          ((biprod.inl : I₁.cocomplex.X (n + 1) ⟶
            I₁.cocomplex.X (n + 1) ⊞ I₃.cocomplex.X (n + 1)) ≫
            (biprod.fst : I₁.cocomplex.X (n + 1) ⊞ I₃.cocomplex.X (n + 1) ⟶
              I₁.cocomplex.X (n + 1))) :=
      congrArg (I₁.cocomplex.d n (n + 1) ≫ ·) (congrArg (· ≫ biprod.fst) hifS)
    have c4 : I₁.cocomplex.d n (n + 1) ≫
          ((biprod.inl : I₁.cocomplex.X (n + 1) ⟶
            I₁.cocomplex.X (n + 1) ⊞ I₃.cocomplex.X (n + 1)) ≫
            (biprod.fst : I₁.cocomplex.X (n + 1) ⊞ I₃.cocomplex.X (n + 1) ⟶
              I₁.cocomplex.X (n + 1))) =
        I₁.cocomplex.d n (n + 1) ≫ 𝟙 _ :=
      congrArg (I₁.cocomplex.d n (n + 1) ≫ ·) biprod.inl_fst
    have c5 : I₁.cocomplex.d n (n + 1) ≫ 𝟙 _ = I₁.cocomplex.d n (n + 1) :=
      Category.comp_id _
    have e11 : biprod.inl ≫ ((horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) n).inv ≫
          (horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).middle.cocomplex.d n (n + 1) ≫
            (horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) (n + 1)).hom) ≫
          biprod.fst = I₁.cocomplex.d n (n + 1) :=
      c0.trans (c1.trans (c2.trans (c3.trans (c4.trans c5))))
    -- e12 : (inl ≫ D) ≫ snd = 0
    have z0 : biprod.inl ≫ ((horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) n).inv ≫
          (horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).middle.cocomplex.d n (n + 1) ≫
            (horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) (n + 1)).hom) ≫
          biprod.snd =
        (biprod.inl ≫ ((horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) n).inv ≫
            (horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).middle.cocomplex.d n (n + 1) ≫
              (horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) (n + 1)).hom)) ≫
          biprod.snd :=
      (Category.assoc _ _ _).symm
    have z1 : (biprod.inl ≫ ((horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) n).inv ≫
            (horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).middle.cocomplex.d n (n + 1) ≫
              (horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) (n + 1)).hom)) ≫
          biprod.snd =
        (I₁.cocomplex.d n (n + 1) ≫
            ((horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).i.f (n + 1) ≫
              (horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) (n + 1)).hom)) ≫
          biprod.snd :=
      congrArg (· ≫ biprod.snd) eBase
    have z2 : (I₁.cocomplex.d n (n + 1) ≫
            ((horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).i.f (n + 1) ≫
              (horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) (n + 1)).hom)) ≫
          biprod.snd =
        I₁.cocomplex.d n (n + 1) ≫
          (((horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).i.f (n + 1) ≫
              (horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) (n + 1)).hom) ≫
            biprod.snd) :=
      Category.assoc _ _ _
    have z3 : I₁.cocomplex.d n (n + 1) ≫
          (((horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).i.f (n + 1) ≫
              (horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) (n + 1)).hom) ≫
            biprod.snd) =
        I₁.cocomplex.d n (n + 1) ≫
          ((biprod.inl : I₁.cocomplex.X (n + 1) ⟶
            I₁.cocomplex.X (n + 1) ⊞ I₃.cocomplex.X (n + 1)) ≫
            (biprod.snd : I₁.cocomplex.X (n + 1) ⊞ I₃.cocomplex.X (n + 1) ⟶
              I₃.cocomplex.X (n + 1))) :=
      congrArg (I₁.cocomplex.d n (n + 1) ≫ ·) (congrArg (· ≫ biprod.snd) hifS)
    have z4 : I₁.cocomplex.d n (n + 1) ≫
          ((biprod.inl : I₁.cocomplex.X (n + 1) ⟶
            I₁.cocomplex.X (n + 1) ⊞ I₃.cocomplex.X (n + 1)) ≫
            (biprod.snd : I₁.cocomplex.X (n + 1) ⊞ I₃.cocomplex.X (n + 1) ⟶
              I₃.cocomplex.X (n + 1))) =
        I₁.cocomplex.d n (n + 1) ≫
          (0 : I₁.cocomplex.X (n + 1) ⟶ I₃.cocomplex.X (n + 1)) :=
      congrArg (I₁.cocomplex.d n (n + 1) ≫ ·) biprod.inl_snd
    have z5 : I₁.cocomplex.d n (n + 1) ≫
          (0 : I₁.cocomplex.X (n + 1) ⟶ I₃.cocomplex.X (n + 1)) = 0 := comp_zero
    have e12 : biprod.inl ≫ ((horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) n).inv ≫
          (horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).middle.cocomplex.d n (n + 1) ≫
            (horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) (n + 1)).hom) ≫
          biprod.snd = 0 :=
      z0.trans (z1.trans (z2.trans (z3.trans (z4.trans z5))))
    -- k2 : φS.hom ≫ snd = H.p.f (n+1)
    have k2a : (horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) (n + 1)).hom ≫
          biprod.snd =
        (horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) (n + 1)).hom ≫
          ((horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) (n + 1)).inv ≫
            (horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).p.f (n + 1)) :=
      congrArg ((horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) (n + 1)).hom ≫ ·)
        hpfS.symm
    have k2b : (horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) (n + 1)).hom ≫
          ((horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) (n + 1)).inv ≫
            (horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).p.f (n + 1)) =
        ((horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) (n + 1)).hom ≫
            (horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) (n + 1)).inv) ≫
          (horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).p.f (n + 1) :=
      (Category.assoc _ _ _).symm
    have k2c : ((horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) (n + 1)).hom ≫
            (horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) (n + 1)).inv) ≫
          (horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).p.f (n + 1) =
        𝟙 _ ≫ (horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).p.f (n + 1) :=
      congrArg (· ≫ (horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).p.f (n + 1))
        (horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) (n + 1)).hom_inv_id
    have k2d : 𝟙 _ ≫ (horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).p.f (n + 1) =
        (horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).p.f (n + 1) :=
      Category.id_comp _
    have k2 : (horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) (n + 1)).hom ≫
          biprod.snd =
        (horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).p.f (n + 1) :=
      k2a.trans (k2b.trans (k2c.trans k2d))
    -- eBaseP : D ≫ snd = (φn.inv ≫ H.p.f n) ≫ d3
    have p1 : ((horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) n).inv ≫
          (horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).middle.cocomplex.d n (n + 1) ≫
            (horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) (n + 1)).hom) ≫
          biprod.snd =
        (horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) n).inv ≫
          (((horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).middle.cocomplex.d n (n + 1) ≫
              (horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) (n + 1)).hom) ≫
            biprod.snd) :=
      Category.assoc _ _ _
    have p2 : (horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) n).inv ≫
          (((horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).middle.cocomplex.d n (n + 1) ≫
              (horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) (n + 1)).hom) ≫
            biprod.snd) =
        (horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) n).inv ≫
          ((horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).middle.cocomplex.d n (n + 1) ≫
            ((horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) (n + 1)).hom ≫
              biprod.snd)) :=
      congrArg ((horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) n).inv ≫ ·)
        (Category.assoc _ _ _)
    have p3 : (horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) n).inv ≫
          ((horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).middle.cocomplex.d n (n + 1) ≫
            ((horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) (n + 1)).hom ≫
              biprod.snd)) =
        (horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) n).inv ≫
          ((horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).middle.cocomplex.d n (n + 1) ≫
            (horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).p.f (n + 1)) :=
      congrArg ((horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) n).inv ≫ ·)
        (congrArg ((horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).middle.cocomplex.d n
            (n + 1) ≫ ·) k2)
    have p4 : (horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) n).inv ≫
          ((horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).middle.cocomplex.d n (n + 1) ≫
            (horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).p.f (n + 1)) =
        (horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) n).inv ≫
          ((horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).p.f n ≫
            I₃.cocomplex.d n (n + 1)) :=
      congrArg ((horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) n).inv ≫ ·)
        hcp.symm
    have p5 : (horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) n).inv ≫
          ((horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).p.f n ≫
            I₃.cocomplex.d n (n + 1)) =
        ((horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) n).inv ≫
            (horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).p.f n) ≫
          I₃.cocomplex.d n (n + 1) :=
      (Category.assoc _ _ _).symm
    have eBaseP : ((horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) n).inv ≫
          (horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).middle.cocomplex.d n (n + 1) ≫
            (horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) (n + 1)).hom) ≫
          biprod.snd =
        ((horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) n).inv ≫
            (horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).p.f n) ≫
          I₃.cocomplex.d n (n + 1) :=
      p1.trans (p2.trans (p3.trans (p4.trans p5)))
    -- e22 : (inr ≫ D) ≫ snd = d3
    have q0 : biprod.inr ≫ ((horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) n).inv ≫
          (horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).middle.cocomplex.d n (n + 1) ≫
            (horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) (n + 1)).hom) ≫
          biprod.snd =
        (biprod.inr ≫ ((horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) n).inv ≫
            (horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).middle.cocomplex.d n (n + 1) ≫
              (horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) (n + 1)).hom)) ≫
          biprod.snd :=
      (Category.assoc _ _ _).symm
    have q1 : (biprod.inr ≫ ((horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) n).inv ≫
            (horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).middle.cocomplex.d n (n + 1) ≫
              (horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) (n + 1)).hom)) ≫
          biprod.snd =
        biprod.inr ≫ (((horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) n).inv ≫
            (horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).middle.cocomplex.d n (n + 1) ≫
              (horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) (n + 1)).hom) ≫
            biprod.snd) :=
      Category.assoc _ _ _
    have q2 : biprod.inr ≫ (((horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) n).inv ≫
            (horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).middle.cocomplex.d n (n + 1) ≫
              (horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) (n + 1)).hom) ≫
            biprod.snd) =
        biprod.inr ≫ (((horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) n).inv ≫
            (horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).p.f n) ≫
          I₃.cocomplex.d n (n + 1)) :=
      congrArg (biprod.inr ≫ ·) eBaseP
    have q3 : biprod.inr ≫ (((horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) n).inv ≫
            (horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).p.f n) ≫
          I₃.cocomplex.d n (n + 1)) =
        (biprod.inr : I₃.cocomplex.X n ⟶
            I₁.cocomplex.X n ⊞ I₃.cocomplex.X n) ≫
          ((biprod.snd : I₁.cocomplex.X n ⊞ I₃.cocomplex.X n ⟶
            I₃.cocomplex.X n) ≫ I₃.cocomplex.d n (n + 1)) :=
      congrArg (biprod.inr ≫ ·) (congrArg (· ≫ I₃.cocomplex.d n (n + 1)) hpfn)
    have q4 : (biprod.inr : I₃.cocomplex.X n ⟶
            I₁.cocomplex.X n ⊞ I₃.cocomplex.X n) ≫
          ((biprod.snd : I₁.cocomplex.X n ⊞ I₃.cocomplex.X n ⟶
            I₃.cocomplex.X n) ≫ I₃.cocomplex.d n (n + 1)) =
        ((biprod.inr : I₃.cocomplex.X n ⟶
            I₁.cocomplex.X n ⊞ I₃.cocomplex.X n) ≫
          (biprod.snd : I₁.cocomplex.X n ⊞ I₃.cocomplex.X n ⟶
            I₃.cocomplex.X n)) ≫ I₃.cocomplex.d n (n + 1) :=
      (Category.assoc _ _ _).symm
    have q5 : ((biprod.inr : I₃.cocomplex.X n ⟶
            I₁.cocomplex.X n ⊞ I₃.cocomplex.X n) ≫
          (biprod.snd : I₁.cocomplex.X n ⊞ I₃.cocomplex.X n ⟶
            I₃.cocomplex.X n)) ≫ I₃.cocomplex.d n (n + 1) =
        𝟙 _ ≫ I₃.cocomplex.d n (n + 1) :=
      congrArg (· ≫ I₃.cocomplex.d n (n + 1)) biprod.inr_snd
    have q6 : 𝟙 _ ≫ I₃.cocomplex.d n (n + 1) = I₃.cocomplex.d n (n + 1) :=
      Category.id_comp _
    have e22 : biprod.inr ≫ ((horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) n).inv ≫
          (horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).middle.cocomplex.d n (n + 1) ≫
            (horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) (n + 1)).hom) ≫
          biprod.snd = I₃.cocomplex.d n (n + 1) :=
      q0.trans (q1.trans (q2.trans (q3.trans (q4.trans (q5.trans q6)))))
    -- assembly via ofComponents_eq
    have hD : ((horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) n).inv ≫
          (horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).middle.cocomplex.d n (n + 1) ≫
            (horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) (n + 1)).hom) =
        Biprod.ofComponents
          (biprod.inl ≫ ((horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) n).inv ≫
            (horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).middle.cocomplex.d n (n + 1) ≫
              (horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) (n + 1)).hom) ≫
            biprod.fst)
          (biprod.inl ≫ ((horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) n).inv ≫
            (horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).middle.cocomplex.d n (n + 1) ≫
              (horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) (n + 1)).hom) ≫
            biprod.snd)
          (biprod.inr ≫ ((horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) n).inv ≫
            (horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).middle.cocomplex.d n (n + 1) ≫
              (horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) (n + 1)).hom) ≫
            biprod.fst)
          (biprod.inr ≫ ((horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) n).inv ≫
            (horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).middle.cocomplex.d n (n + 1) ≫
              (horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) (n + 1)).hom) ≫
            biprod.snd) :=
      (Biprod.ofComponents_eq _).symm
    exact hD.trans (by rw [e11, e12, e22])


/-- For a short exact sequence `S` in an abelian category `C` and injective
endpoint resolutions `I₁`, `I₃`, the degree-zero horseshoe inclusion respects
the augmentation: `I₁.ι₀ ≫ i₀ = S.f ≫ middle.ι₀`. -/
theorem horseshoe_i_comm :
    I₁.ι.f 0 ≫ (horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).i.f 0 =
      S.f ≫ (horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).middle.ι.f 0 := by
  have h := HomologicalComplex.congr_hom
    (horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).i_augmentation 0
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    CochainComplex.single₀_map_f_zero] at h
  exact h

/-- For a short exact sequence `S` in an abelian category `C` and injective
endpoint resolutions `I₁`, `I₃`, the degree-zero horseshoe projection respects
the augmentation: `middle.ι₀ ≫ p₀ = S.g ≫ I₃.ι₀`. -/
theorem horseshoe_p_comm :
    (horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).middle.ι.f 0 ≫
        (horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).p.f 0 =
      S.g ≫ I₃.ι.f 0 := by
  have h := HomologicalComplex.congr_hom
    (horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).p_augmentation 0
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    CochainComplex.single₀_map_f_zero] at h
  exact h

/-- For a short exact sequence `S` in an abelian category `C` and injective
resolutions `I₁` of `S.X₁`, `I₃` of `S.X₃`, the constructed resolution of
`S.X₂` fits into a short exact sequence `I₁.cocomplex → middle.cocomplex →
I₃.cocomplex` in the abelian category of natural-index cochain complexes. -/
theorem horseshoe_shortExact {S : ShortComplex C} (hS : S.ShortExact)
    (I₁ : InjectiveResolution S.X₁) (I₃ : InjectiveResolution S.X₃) :
    (ShortComplex.mk
      (horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).i
      (horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).p
      (horseshoe (hS := hS) (I₁ := I₁)
        (I₃ := I₃)).zero).ShortExact :=
  (horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).shortExact

/-- For a short exact sequence `S` in an abelian category `C` and injective
endpoint resolutions `I₁`, `I₃`, this compatibility name denotes the same
degreewise isomorphism from the horseshoe middle term to `I₁ⁿ ⊞ I₃ⁿ` as
`horseshoeMiddleXIso`. -/
@[deprecated horseshoeMiddleXIso (since := "2026-11-09"), nolint defsWithUnderscore]
noncomputable abbrev horseshoe_middle_X_iso (n : ℕ) :
    (horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).middle.cocomplex.X n ≅
      I₁.cocomplex.X n ⊞ I₃.cocomplex.X n :=
  horseshoeMiddleXIso (hS := hS) (I₁ := I₁) (I₃ := I₃) n

/-- For a short exact sequence `S` in an abelian category `C` and injective
endpoint resolutions `I₁`, `I₃`, this compatibility name denotes the canonical
biproduct and triangular-differential specification of the constructed
horseshoe, also named `horseshoeSpec`. -/
@[deprecated horseshoeSpec (since := "2026-11-09"), nolint defsWithUnderscore]
noncomputable abbrev horseshoe_spec :
    (horseshoe (hS := hS) (I₁ := I₁) (I₃ := I₃)).Spec :=
  horseshoeSpec (hS := hS) (I₁ := I₁) (I₃ := I₃)

end CategoryTheory.InjectiveResolution
