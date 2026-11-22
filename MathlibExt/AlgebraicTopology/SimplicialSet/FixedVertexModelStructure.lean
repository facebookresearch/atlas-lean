/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition
public import Mathlib.CategoryTheory.MorphismProperty.WeakFactorizationSystem
public import MathlibExt.AlgebraicTopology.SimplicialSet.FixedVertex
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.HoPreNatIso
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SmallObject
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.InnerAnodyneCategorical

/-!
# Fixed-vertex lifting classes and weak factorization systems

For `SSet.FixedVertex O` this file develops vertex-bijective maps, reflection
of lifting problems along the forgetful functor, and the underlying classes
of inner-anodyne maps and trivial Kan fibrations. It proves the weak
factorization system of inner-anodyne maps and inner fibrations. Monomorphisms
and trivial Kan fibrations form a weak factorization system under the explicit
factorization hypothesis. The fixed-vertex category also has finite limits
and finite colimits.

The inclusion of inner-anodyne maps in monic categorical equivalences and the
inclusion of trivial Kan fibrations in categorical inner fibrations are valid.
Their reverse inclusions fail already for `O = Fin 2`, by Campbell's
counterexample. Consequently these two weak factorization systems do not
identify the fibrations of a model structure with all inner fibrations.
A model structure with monic cofibrations and categorical weak equivalences
must instead use their internal right lifting class; its construction and
comparison are separate obligations.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory Limits MorphismProperty Opposite
open scoped Simplicial

namespace SSet

/-! ### Inner anodyne extensions are vertex-bijective -/

/-- The morphism property of vertex-bijective simplicial maps
(`SSet.IsVertexBijective`), as a `MorphismProperty` for saturation
arguments. -/
def vertexBijective : MorphismProperty SSet.{u} :=
  fun _ _ f => IsVertexBijective f

/-- A simplicial map is vertex-bijective if and only if its degree-`0`
component, seen through the evaluation functor, is an isomorphism of
types. -/
lemma vertexBijective_iff_isIso {X Y : SSet.{u}} (f : X ⟶ Y) :
    vertexBijective.{u} f ↔ IsIso (((evaluation SimplexCategoryᵒᵖ (Type u)).obj
      (op ⦋0⦌)).map f) := by
  rw [isIso_iff_bijective]
  exact Iff.rfl

/-- Vertex-bijective maps contain the identities. -/
instance : vertexBijective.{u}.ContainsIdentities where
  id_mem X := isVertexBijective_id X

/-- Vertex-bijective maps are stable under composition. -/
instance : vertexBijective.{u}.IsStableUnderComposition where
  comp_mem _ _ hf hg := hf.comp hg

/-- Vertex-bijective maps are multiplicative. -/
instance : vertexBijective.{u}.IsMultiplicative where

/-- Vertex-bijective maps respect isomorphisms. -/
instance : vertexBijective.{u}.RespectsIso :=
  respectsIso_of_isStableUnderComposition (fun X Y f hf => by
    have : IsIso f := hf
    rw [vertexBijective_iff_isIso]
    infer_instance)

/-- Vertex-bijective maps are stable under colimits of any shape
admitting colimits in `Type u`: evaluation at `⦋0⦌` preserves
colimits, and isomorphisms of types are stable under colimits. -/
instance isStableUnderColimitsOfShape_vertexBijective
    {J : Type v} [Category.{v} J] [HasColimitsOfShape J (Type u)] :
    vertexBijective.{u}.IsStableUnderColimitsOfShape J where
  condition X₁ X₂ c₁ c₂ h₁ h₂ f hf φ hφ := by
    rw [vertexBijective_iff_isIso]
    let E := (evaluation SimplexCategoryᵒᵖ (Type u)).obj (op ⦋0⦌)
    let fE : X₁ ⋙ E ⟶ X₂ ⋙ E :=
      { app j := E.map (f.app j)
        naturality j j' t := by
          change E.map (X₁.map t) ≫ E.map (f.app j') =
            E.map (f.app j) ≫ E.map (X₂.map t)
          rw [← E.map_comp, ← E.map_comp, f.naturality] }
    have hf' : (MorphismProperty.isomorphisms (Type u)).functorCategory J fE := by
      intro j
      change IsIso (E.map (f.app j))
      rw [← vertexBijective_iff_isIso]
      exact hf j
    exact IsStableUnderColimitsOfShape.condition
      (X₁ ⋙ E) (X₂ ⋙ E) (E.mapCocone c₁) (E.mapCocone c₂)
      (isColimitOfPreserves E h₁) (isColimitOfPreserves E h₂)
      fE hf' (E.map φ) (fun j => by
        change E.map (c₁.ι.app j) ≫ E.map φ = E.map (f.app j) ≫ E.map (c₂.ι.app j)
        rw [← E.map_comp, ← E.map_comp, hφ j])

/-- Vertex-bijective maps are stable under coproducts. -/
instance : IsStableUnderCoproducts.{u} vertexBijective.{u} where
  isStableUnderCoproductsOfShape J := by infer_instance

/-- Vertex-bijective maps are stable under cobase change: a pushout
of an isomorphism of types is an isomorphism, degreewise. -/
instance : vertexBijective.{u}.IsStableUnderCobaseChange where
  of_isPushout {A A' B B' f g f' g'} sq hf := by
    rw [vertexBijective_iff_isIso] at hf ⊢
    exact (MorphismProperty.isomorphisms (Type u)).of_isPushout
      (sq.map ((evaluation SimplexCategoryᵒᵖ (Type u)).obj (op ⦋0⦌))) hf

/-- Vertex-bijective maps are stable under retracts. -/
instance : vertexBijective.{u}.IsStableUnderRetracts where
  of_retract h hg := by
    rw [vertexBijective_iff_isIso] at hg ⊢
    exact MorphismProperty.of_retract (h.map _) hg

/-- Vertex-bijective maps are stable under transfinite compositions
of shape `ℕ`: the cocone leg at `⊥` is a colimit of vertex-bijective
maps out of the bottom object, each built by induction from the
successor steps. -/
instance : vertexBijective.{u}.IsStableUnderTransfiniteCompositionOfShape ℕ where
  le := by
    intro X Y f hf
    obtain ⟨h⟩ := hf
    have hbot : ∀ j : ℕ, vertexBijective.{u} (h.F.map (homOfLE (bot_le : ⊥ ≤ j))) := by
      intro j
      induction j with
      | zero =>
        have h0 : (homOfLE (bot_le : (⊥ : ℕ) ≤ 0)) = 𝟙 (⊥ : ℕ) := Subsingleton.elim _ _
        rw [h0, h.F.map_id]
        exact vertexBijective.{u}.id_mem _
      | succ j ih =>
        rw [← homOfLE_comp bot_le (Nat.le_succ j), h.F.map_comp]
        exact vertexBijective.{u}.comp_mem _ _ ih (h.map_mem j
          (fun hmax => Nat.not_succ_le_self j (hmax (Nat.le_succ j))))
    have hmem : vertexBijective.{u} (h.incl.app ⊥) :=
      vertexBijective.{u}.colimitsOfShape_le _
        (MorphismProperty.colimitsOfShape.of_isColimit h.isColimit hbot)
    exact (vertexBijective.{u}.arrow_mk_iso_iff
      (Arrow.isoMk h.isoBot.symm (Iso.refl _) (by simpa using h.fac))).2 hmem

/-- Inner horn inclusions are bijective on vertices (in the shifted
form `Λ[n + 2, i]` used by `SSet.innerHornInclusions`): injectivity
is the subcomplex inclusion, and surjectivity is
`SSet.horn_obj_zero` (in degree `0` the horn is everything). -/
lemma bijective_horn_ι_app_zero {n : ℕ} {i : Fin (n + 3)} :
    Function.Bijective (Λ[n + 2, i].ι.app (op ⦋0⦌)) :=
  ⟨fun a b hab => Subtype.ext hab, fun s => ⟨⟨s, by
    rw [SSet.horn_obj_zero]
    trivial⟩, rfl⟩⟩

/-- The generating inner horn inclusions are vertex-bijective. -/
lemma innerHornInclusions_le_vertexBijective :
    innerHornInclusions.{u} ≤ vertexBijective.{u} := by
  intro X Y f hf
  obtain ⟨i, -, -⟩ := hf
  exact bijective_horn_ι_app_zero

/-- **Inner anodyne extensions are vertex-bijective**
(Stevenson §5.1: inner horn inclusions, hence all inner anodyne maps,
are bijective on vertices). Proved by weak saturation from
`SSet.innerAnodyneExtensions_eq_retracts_transfiniteCompositionsOfShape`
and stability of vertex-bijective maps under retracts, transfinite
compositions of shape `ℕ`, cobase change and coproducts. -/
theorem innerAnodyneExtensions_le_vertexBijective :
    innerAnodyneExtensions.{u} ≤ vertexBijective.{u} := by
  rw [innerAnodyneExtensions_eq_retracts_transfiniteCompositionsOfShape,
    MorphismProperty.retracts_le_iff]
  exact le_trans
    (MorphismProperty.transfiniteCompositionsOfShape_monotone ℕ
      (MorphismProperty.pushouts_le_iff.2
        (MorphismProperty.coproducts_le_iff.2
          innerHornInclusions_le_vertexBijective)))
    (MorphismProperty.transfiniteCompositionsOfShape_le vertexBijective.{u} ℕ)

/-- Membership form of `SSet.innerAnodyneExtensions_le_vertexBijective`:
an inner anodyne extension is vertex-bijective. -/
theorem isVertexBijective_of_innerAnodyneExtensions {X Y : SSet.{u}} {f : X ⟶ Y}
    (hf : innerAnodyneExtensions f) : IsVertexBijective f :=
  innerAnodyneExtensions_le_vertexBijective f hf

/-- Inner anodyne extensions of simplicial sets are monomorphisms:
they are anodyne extensions, which are monomorphisms by the
`llp`/`rlp` computation against `I` (as in the Quillen model
structure). -/
lemma innerAnodyneExtensions_le_monomorphisms_of_llp :
    innerAnodyneExtensions.{u} ≤ monomorphisms SSet.{u} := by
  refine le_trans innerAnodyneExtensions_le ?_
  rw [anodyneExtensions_eq_llp_rlp, ← modelCategoryQuillen.llp_rlp_I,
    ← rlp_monomorphisms]
  exact antitone_llp (antitone_rlp modelCategoryQuillen.J_le_monomorphisms)

end SSet

namespace SSet.FixedVertex

variable {O : Type u} {X Y Z : FixedVertex O}

/-! ### The four classes in `SSet(O)` -/

/-- Trivial Kan fibrations in `SSet(O)`: by Stevenson's convention
(§5.3), a map in `SSet(O)` is a trivial Kan fibration just in case its
underlying simplicial map has the right lifting property against the
boundary inclusions `SSet.modelCategoryQuillen.I`. This is
Stevenson's class `ℱ_𝒲`. -/
def trivialKanFibrations (O : Type u) : MorphismProperty (FixedVertex O) :=
  MorphismProperty.inverseImage SSet.modelCategoryQuillen.I.rlp (forget O)

/-- Membership in `trivialKanFibrations O` is by definition the
trivial Kan fibration property of the underlying simplicial map. -/
theorem trivialKanFibrations_mem_iff (f : X ⟶ Y) :
    trivialKanFibrations O f ↔
      SSet.modelCategoryQuillen.I.rlp ((forget O).map f) :=
  Iff.rfl

/-- Inner anodyne maps in `SSet(O)`: by Stevenson's convention, a map
in `SSet(O)` is inner anodyne just in case its underlying simplicial
map is an inner anodyne extension. This is Stevenson's class `𝒞_𝒲`. -/
def innerAnodyne (O : Type u) : MorphismProperty (FixedVertex O) :=
  MorphismProperty.inverseImage SSet.innerAnodyneExtensions (forget O)

/-- Membership in `innerAnodyne O` is by definition the inner
anodyne property of the underlying simplicial map. -/
theorem innerAnodyne_mem_iff (f : X ⟶ Y) :
    innerAnodyne O f ↔ SSet.innerAnodyneExtensions ((forget O).map f) :=
  Iff.rfl

/-- Categorical equivalences in `SSet(O)` are stable under retracts,
by inverse image from `SSet`. -/
instance : (categoricalEquivalences O).IsStableUnderRetracts :=
  inferInstanceAs ((SSet.categoricalEquivalences.inverseImage
    (forget O)).IsStableUnderRetracts)

/-- Categorical equivalences in `SSet(O)` are stable under
composition, by inverse image from `SSet`. -/
instance : (categoricalEquivalences O).IsStableUnderComposition :=
  inferInstanceAs ((SSet.categoricalEquivalences.inverseImage
    (forget O)).IsStableUnderComposition)

/-- Left cancellation for categorical equivalences in `SSet(O)`,
by inverse image from `SSet`. -/
instance : (categoricalEquivalences O).HasOfPostcompProperty
    (categoricalEquivalences O) where
  of_postcomp f g hg hfg :=
    MorphismProperty.of_postcomp SSet.categoricalEquivalences
      ((forget O).map f) ((forget O).map g) hg ((categoricalEquivalences_mem_iff (f ≫ g)).1 hfg)

/-- Right cancellation for categorical equivalences in `SSet(O)`,
by inverse image from `SSet`. -/
instance : (categoricalEquivalences O).HasOfPrecompProperty
    (categoricalEquivalences O) where
  of_precomp f g hf hfg :=
    MorphismProperty.of_precomp SSet.categoricalEquivalences
      ((forget O).map f) ((forget O).map g) hf ((categoricalEquivalences_mem_iff (f ≫ g)).1 hfg)

/-- Categorical equivalences in `SSet(O)` have the two-out-of-three
property (Stevenson's "clearly `𝒲` satisfies the 2-out-of-3 property"
in the proof of Theorem 5.12). -/
instance : (categoricalEquivalences O).HasTwoOutOfThreeProperty where

/-- Inner fibrations in `SSet(O)` are stable under retracts. -/
instance : (innerFibrations O).IsStableUnderRetracts :=
  inferInstanceAs ((SSet.innerHornInclusions.rlp.inverseImage
    (forget O)).IsStableUnderRetracts)

/-- Trivial Kan fibrations in `SSet(O)` are stable under retracts. -/
instance : (trivialKanFibrations O).IsStableUnderRetracts :=
  inferInstanceAs ((SSet.modelCategoryQuillen.I.rlp.inverseImage
    (forget O)).IsStableUnderRetracts)

/-- Inner anodyne maps in `SSet(O)` are stable under retracts. -/
instance : (innerAnodyne O).IsStableUnderRetracts :=
  inferInstanceAs ((SSet.innerHornInclusions.rlp.llp.inverseImage
    (forget O)).IsStableUnderRetracts)

/-- The easy inclusion `𝒞_𝒲 ⊆ 𝒞 ∩ 𝒲` of Stevenson's proof: an inner
anodyne map in `SSet(O)` is a monomorphism and a categorical
equivalence. In `SSet` these are
`SSet.innerAnodyneExtensions_le_monomorphisms_of_llp` and the theorem
that inner anodyne extensions are categorical equivalences (the supporting result). -/
theorem innerAnodyne_le :
    innerAnodyne O ≤ monomorphisms (FixedVertex O) ⊓ categoricalEquivalences O := by
  intro A B f hf
  refine ⟨(mono_iff_mono_forget f).2
    (SSet.innerAnodyneExtensions_le_monomorphisms_of_llp _ hf), ?_⟩
  exact SSet.innerAnodyneExtensions_le_categoricalEquivalences _ hf

/-- The easy inclusion `ℱ_𝒲 ⊆ ℱ ∩ 𝒲` of Stevenson's proof: a trivial
Kan fibration in `SSet(O)` is an inner fibration and a categorical
equivalence. In `SSet`: maps with the right lifting property against
all boundary inclusions have it against inner horns (which are
monomorphisms), and trivial Kan fibrations are categorical
equivalences (the supporting result). -/
theorem trivialKanFibrations_le :
    trivialKanFibrations O ≤ innerFibrations O ⊓ categoricalEquivalences O := by
  intro A B f hf
  refine ⟨?_, SSet.modelCategoryQuillen_I_rlp_le_categoricalEquivalences _ hf⟩
  have h1 : SSet.modelCategoryQuillen.I.rlp ≤ SSet.innerHornInclusions.rlp := by
    rw [← SSet.rlp_monomorphisms]
    apply MorphismProperty.antitone_rlp
    intro P Q g hg
    obtain ⟨i, -, -⟩ := hg
    exact inferInstance
  exact h1 _ hf

/-! ### Lifting reflects along the forgetful functor -/

/-- **Lifting reflects from `SSet` to `SSet(O)`.** If the underlying
simplicial maps have the lifting property, so do the maps in
`SSet(O)`: a filler in `SSet` is automatically compatible with the
vertex identifications, because the left map of the square is
surjective (indeed bijective) on vertices, being a morphism of
`SSet(O)`. This is the fixed-vertex form of the observation behind
Lemma 5.11 that lifting in `SSet(O)` is detected in `SSet`. -/
theorem hasLiftingProperty_of_forget {A B X Y : FixedVertex O}
    {i : A ⟶ B} {p : X ⟶ Y}
    (h : HasLiftingProperty i.hom p.hom) : HasLiftingProperty i p where
  sq_hasLift {t b} sq := by
    let sq' : CommSq t.hom i.hom p.hom b.hom := CommSq.mk (congrArg Hom.hom sq.w)
    have : sq'.HasLift := h.sq_hasLift sq'
    refine ⟨⟨{ l := liftHom sq'.lift (fun v => ?_)
               fac_left := hom_ext sq'.fac_left
               fac_right := hom_ext sq'.fac_right }⟩⟩
    obtain ⟨a, ha'⟩ := (forget_map_isVertexBijective i).2 v
    have ha : i.hom.app (op ⦋0⦌) a = v := ha'
    have hfac : sq'.lift.app (op ⦋0⦌) (i.hom.app (op ⦋0⦌) a) =
        t.hom.app (op ⦋0⦌) a := by
      have hh : (i.hom ≫ sq'.lift).app (op ⦋0⦌) a = t.hom.app (op ⦋0⦌) a :=
        ConcreteCategory.congr_hom (congr_app sq'.fac_left (op ⦋0⦌)) a
      exact hh
    calc X.vertexEquiv (sq'.lift.app (op ⦋0⦌) v)
        = X.vertexEquiv (t.hom.app (op ⦋0⦌) a) := by rw [← ha, hfac]
      _ = A.vertexEquiv a := t.w a
      _ = B.vertexEquiv v := by rw [← ha]; exact (i.w a).symm

/-! ### The `(innerAnodyne, innerFibrations)` weak factorization system -/

/-- The factorization of the underlying simplicial map of `f` into an
inner anodyne map followed by an inner fibration, from the small
object argument for inner horn inclusions in `SSet`. -/
noncomputable def sSetInnerFactorizationData (f : X ⟶ Y) :
    (SSet.innerHornInclusions.rlp.llp).MapFactorizationData
      SSet.innerHornInclusions.rlp f.hom :=
  MorphismProperty.factorizationData _ _ _

/-- The left factor of `sSetInnerFactorizationData` is an inner
anodyne extension. -/
lemma innerAnodyneExtensions_sSetInnerFactorizationData_i (f : X ⟶ Y) :
    SSet.innerAnodyneExtensions (sSetInnerFactorizationData f).i := by
  rw [SSet.innerAnodyneExtensions_eq_llp_rlp]
  exact (sSetInnerFactorizationData f).hi

/-- The middle object of the lifted factorization, as an object of
`SSet(O)`: the middle simplicial set of the `SSet` factorization, with
vertex identification transported along the left factor, which is
vertex-bijective because inner anodyne extensions are
(`SSet.isVertexBijective_of_innerAnodyneExtensions`). This is the
point at which the inner horn small object argument in `SSet` —
attaching only inner horns, never creating vertices — descends to
`SSet(O)`. -/
noncomputable def innerAnodyneFactorizationObj (f : X ⟶ Y) : FixedVertex O where
  underlying := (sSetInnerFactorizationData f).Z
  vertexEquiv :=
    (Equiv.ofBijective _
      (SSet.isVertexBijective_of_innerAnodyneExtensions
        (innerAnodyneExtensions_sSetInnerFactorizationData_i f))).symm.trans
      X.vertexEquiv

/-- The vertex identification of the middle object sends the image of
a vertex of `X` under the left factor to its label in `X`. -/
lemma innerAnodyneFactorizationObj_vertexEquiv_i_app (f : X ⟶ Y)
    (vtx : X.underlying _⦋0⦌) :
    (innerAnodyneFactorizationObj f).vertexEquiv
        ((sSetInnerFactorizationData f).i.app (op ⦋0⦌) vtx) =
      X.vertexEquiv vtx :=
  congrArg X.vertexEquiv (Equiv.symm_apply_apply _ vtx)

/-- The left factor of the lifted factorization, as a morphism of
`SSet(O)`. It is inner anodyne in `SSet(O)` by construction. -/
noncomputable def innerAnodyneFactorizationI (f : X ⟶ Y) :
    X ⟶ innerAnodyneFactorizationObj f :=
  liftHom (sSetInnerFactorizationData f).i
    (fun vtx => innerAnodyneFactorizationObj_vertexEquiv_i_app f vtx)

/-- The underlying simplicial map of `innerAnodyneFactorizationI` is
the left factor in `SSet`. -/
@[simp]
lemma innerAnodyneFactorizationI_hom (f : X ⟶ Y) :
    (innerAnodyneFactorizationI f).hom = (sSetInnerFactorizationData f).i :=
  rfl

/-- The right factor of the lifted factorization, as a morphism of
`SSet(O)`. Its vertex compatibility follows from that of the left
factor and of `f`, using vertex-bijectivity of the left factor. It is
an inner fibration in `SSet(O)` by construction. -/
noncomputable def innerAnodyneFactorizationP (f : X ⟶ Y) :
    innerAnodyneFactorizationObj f ⟶ Y :=
  liftHom (sSetInnerFactorizationData f).p (fun z => by
    obtain ⟨vtx, hv⟩ :=
      (SSet.isVertexBijective_of_innerAnodyneExtensions
        (innerAnodyneExtensions_sSetInnerFactorizationData_i f)).2 z
    have hfac : (sSetInnerFactorizationData f).p.app (op ⦋0⦌)
          ((sSetInnerFactorizationData f).i.app (op ⦋0⦌) vtx) =
        f.hom.app (op ⦋0⦌) vtx := by
      have hh : ((sSetInnerFactorizationData f).i ≫
            (sSetInnerFactorizationData f).p).app (op ⦋0⦌) vtx =
          f.hom.app (op ⦋0⦌) vtx :=
        ConcreteCategory.congr_hom
          (congr_app (sSetInnerFactorizationData f).fac (op ⦋0⦌)) vtx
      exact hh
    calc Y.vertexEquiv ((sSetInnerFactorizationData f).p.app (op ⦋0⦌) z)
        = Y.vertexEquiv (f.hom.app (op ⦋0⦌) vtx) := by rw [← hv, hfac]
      _ = X.vertexEquiv vtx := f.w vtx
      _ = (innerAnodyneFactorizationObj f).vertexEquiv z := by
          rw [← hv]
          exact (innerAnodyneFactorizationObj_vertexEquiv_i_app f vtx).symm)

/-- The underlying simplicial map of `innerAnodyneFactorizationP` is
the right factor in `SSet`. -/
@[simp]
lemma innerAnodyneFactorizationP_hom (f : X ⟶ Y) :
    (innerAnodyneFactorizationP f).hom = (sSetInnerFactorizationData f).p :=
  rfl

/-- The factorization of a morphism of `SSet(O)` as an inner anodyne
map followed by an inner fibration, lifted from `SSet`. -/
noncomputable def innerAnodyneFactorizationData (f : X ⟶ Y) :
    (innerAnodyne O).MapFactorizationData (innerFibrations O) f where
  Z := innerAnodyneFactorizationObj f
  i := innerAnodyneFactorizationI f
  p := innerAnodyneFactorizationP f
  fac := hom_ext (sSetInnerFactorizationData f).fac
  hi := innerAnodyneExtensions_sSetInnerFactorizationData_i f
  hp := (sSetInnerFactorizationData f).hp

/-- Every morphism of `SSet(O)` factors as an inner anodyne map
followed by an inner fibration. -/
instance : (innerAnodyne O).HasFactorization (innerFibrations O) :=
  ⟨fun f => ⟨innerAnodyneFactorizationData f⟩⟩

/-- The weak factorization system of inner-anodyne maps and inner fibrations on `SSet(O)`,
unconditionally: inner anodyne maps against inner fibrations.
Stevenson obtains this from the small object argument for labelled
inner horns in `sSet(O)`; here it is lifted from the corresponding
factorization in `SSet`, using that inner anodyne extensions are
vertex-bijective and that lifting reflects along `forget`. -/
theorem isWeakFactorizationSystem_innerAnodyne_innerFibrations :
    (innerAnodyne O).IsWeakFactorizationSystem (innerFibrations O) :=
  MorphismProperty.IsWeakFactorizationSystem.mk' _ _ (fun i p hi hp =>
    hasLiftingProperty_of_forget (by
      have hi0 : SSet.innerAnodyneExtensions i.hom := hi
      rw [SSet.innerAnodyneExtensions_eq_llp_rlp] at hi0
      exact hi0 _ hp))

/-- The weak factorization system of monomorphisms and trivial Kan fibrations on `SSet(O)`,
conditional on the factorization: given that every morphism of
`SSet(O)` factors as a monomorphism followed by a trivial Kan
fibration (the conclusion of the small object argument for `I_O` in
Stevenson's proof), monomorphisms and trivial Kan fibrations form a
weak factorization system. The lifting is unconditional here: it
reflects from `SSet`, where monomorphisms are exactly the maps with
the left lifting property against trivial Kan fibrations
(`SSet.rlp_monomorphisms`), and monomorphisms are detected in `SSet`
by `mono_iff_mono_forget`. -/
theorem isWeakFactorizationSystem_monomorphisms_trivialKanFibrations
    [(monomorphisms (FixedVertex O)).HasFactorization (trivialKanFibrations O)] :
    (monomorphisms (FixedVertex O)).IsWeakFactorizationSystem
      (trivialKanFibrations O) :=
  MorphismProperty.IsWeakFactorizationSystem.mk' _ _ (fun i p hi hp =>
    hasLiftingProperty_of_forget (by
      have hp' : (monomorphisms SSet.{u}).rlp p.hom := by
        rw [SSet.rlp_monomorphisms]
        exact hp
      exact hp' _ ((mono_iff_mono_forget i).1 hi)))

/-! ### Finite limits and colimits in `SSet(O)` -/

/-- `SSet(O)` has finite limits, from the terminal codiscrete object
and pullbacks computed in `SSet`. -/
instance : HasFiniteLimits (FixedVertex O) :=
  hasFiniteLimits_of_hasTerminal_and_pullbacks

/-- `SSet(O)` has finite colimits, from the initial discrete object
and pushouts computed in `SSet`. -/
instance : HasFiniteColimits (FixedVertex O) :=
  hasFiniteColimits_of_hasInitial_and_pushouts

end FixedVertex

end SSet
