/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.MappingSpaceCategorical
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FundamentalGroupoidPiOne
public import MathlibExt.AlgebraicTopology.Quasicategory.CategoricalProbes

/-!
# Mapping-space weak equivalences from categorical probes

This module constructs internal postcomposition and proves equivalence
on the ordinary homotopy categories of arbitrary functor probes.
`SSet.dwyerKanFullyFaithfulProbes` records full faithfulness on those
probes, with its identity, composition, and two-out-of-six laws.
The Whitehead assembly below accepts explicit connected-component and
positive based homotopy-group bijections on the actual right mapping
spaces. Those hypotheses remain part of these general lemmas.

For maps between quasicategories, the unconditional same-map conclusion
is proved downstream in `RightMappingBrown.lean`:
`SSet.categoricalEquivalences.rightMappingSpaceMap_weak`.
`DwyerKanRecognition.lean` proves the complete equivalence
`SSet.categoricalEquivalences_iff_isDwyerKanEquivalence`, reexported by
`DwyerKanFinal.lean`. Thus the probe lemmas' additional hypotheses are
specific to their relative simplex route. They are not prerequisites
for the complete recognition theorem. `MappingSpacePiPositive.lean`,
`MappingSpaceWUnconditional.lean`, and `DwyerKanFinal.lean` describe the
relative simplex conditions and their obstruction.
-/

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory MonoidalClosed Limits Opposite

open scoped Simplicial

universe u

namespace SSet

variable {X Y Z : SSet.{u}} {f : X ⟶ Y}

/-!
## Internal postcomposition
-/

/-- The internal postcomposition map
`Fun(X, X) ⟶ Fun(Fun(K, X), Fun(K, X))`: the curry of the
internal composition `MonoidalClosed.comp K X X`. Its uncurried
form is composition `Fun(K, X) ⊗ Fun(X, X) ⟶ Fun(K, X)`, and on
vertices it sends the vertex classified by `φ : X ⟶ X` to the
vertex classified by postcomposition `(ihom K).map φ`
(`SSet.ihomPostcompositionMap_app_ihomVertexEquiv`). -/
noncomputable def ihomPostcompositionMap (K X : SSet.{u}) :
    (ihom X).obj X ⟶ (ihom ((ihom K).obj X)).obj ((ihom K).obj X) :=
  MonoidalClosed.curry (MonoidalClosed.comp K X X)

/-- Uncurrying the internal postcomposition map recovers internal
composition. -/
lemma uncurry_ihomPostcompositionMap (K X : SSet.{u}) :
    MonoidalClosed.uncurry (ihomPostcompositionMap K X) =
      MonoidalClosed.comp K X X := by
  simp only [ihomPostcompositionMap, MonoidalClosed.uncurry_curry]

/-- The curried name of `φ : X ⟶ X`, followed by internal
postcomposition, is the curried name of postcomposition with
`φ`. The proof uncurries and uses
`MonoidalClosed.whiskerLeft_curry'_comp`. -/
lemma curry'_comp_ihomPostcompositionMap (K X : SSet.{u}) (φ : X ⟶ X) :
    MonoidalClosed.curry' φ ≫ ihomPostcompositionMap K X =
      MonoidalClosed.curry' ((ihom K).map φ) := by
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left, uncurry_ihomPostcompositionMap,
    MonoidalClosed.whiskerLeft_curry'_comp]
  simp [MonoidalClosed.curry']

/-- The vertex formula for internal postcomposition: the image of
the vertex of `Fun(X, X)` classified by `φ` is the vertex of
`Fun(Fun(K, X), Fun(K, X))` classified by `(ihom K).map φ`. -/
lemma ihomPostcompositionMap_app_ihomVertexEquiv (K X : SSet.{u})
    (φ : X ⟶ X) :
    (ihomPostcompositionMap K X).app (op ⦋0⦌) (ihomVertexEquiv X X φ) =
      ihomVertexEquiv ((ihom K).obj X) ((ihom K).obj X) ((ihom K).map φ) :=
  congrArg (fun ψ : 𝟙_ SSet.{u} ⟶
      (ihom ((ihom K).obj X)).obj ((ihom K).obj X) => ψ.app _ PUnit.unit)
    (curry'_comp_ihomPostcompositionMap K X φ)

/-!
## Postcomposition preserves categorical equivalences
-/

/-- The object formula for `SSet.hoFunctor.map` at a vertex
object. (The underlying functor is `SSet.mapHomotopyCategory` by
definition.) -/
private lemma hoFunctor_map_obj_mk' {A B : SSet.{u}} (θ : A ⟶ B)
    (v : A _⦋0⦌) :
    (hoFunctor.map θ).toFunctor.obj (HomotopyCategory.mk v) =
      HomotopyCategory.mk (θ.app _ v) :=
  mapHomotopyCategory_obj_mk θ v

/-- **Postcomposition preserves homotopy inverses**: if `f` has a
homotopy inverse in the sense of `SSet.HasHoInverse`, then so
does `(ihom K).map f` for every probe `K`, with inverse
`(ihom K).map g`. The witnessing isomorphisms are the images of
the original ones under `h` of the internal postcomposition maps
`SSet.ihomPostcompositionMap K X` and `K Y`, read at vertices by
`SSet.ihomPostcompositionMap_app_ihomVertexEquiv`. -/
theorem HasHoInverse.ihomMap (K : SSet.{u}) (h : HasHoInverse f) :
    HasHoInverse ((ihom K).map f) := by
  obtain ⟨g, ⟨α⟩, ⟨β⟩⟩ := h
  refine ⟨(ihom K).map g, ⟨?_⟩, ⟨?_⟩⟩
  · have hα := (hoFunctor.map (ihomPostcompositionMap K X)).toFunctor.mapIso α
    rw [hoFunctor_map_obj_mk', hoFunctor_map_obj_mk',
      ihomPostcompositionMap_app_ihomVertexEquiv,
      ihomPostcompositionMap_app_ihomVertexEquiv] at hα
    have hcomp : (ihom K).map (f ≫ g) =
        (ihom K).map f ≫ (ihom K).map g :=
      (ihom K).map_comp f g
    have hid : (ihom K).map (𝟙 X) = 𝟙 ((ihom K).obj X) :=
      (ihom K).map_id X
    rw [hcomp, hid] at hα
    exact hα
  · have hβ := (hoFunctor.map (ihomPostcompositionMap K Y)).toFunctor.mapIso β
    rw [hoFunctor_map_obj_mk', hoFunctor_map_obj_mk',
      ihomPostcompositionMap_app_ihomVertexEquiv,
      ihomPostcompositionMap_app_ihomVertexEquiv] at hβ
    have hcomp : (ihom K).map (g ≫ f) =
        (ihom K).map g ≫ (ihom K).map f :=
      (ihom K).map_comp g f
    have hid : (ihom K).map (𝟙 Y) = 𝟙 ((ihom K).obj Y) :=
      (ihom K).map_id Y
    rw [hcomp, hid] at hβ
    exact hβ

/-- **Postcomposition preserves categorical equivalences**: if
`f` between quasicategories is a categorical equivalence, then
`(ihom K).map f : Fun(K, X) ⟶ Fun(K, Y)` is a categorical
equivalence for every probe `K`. Via the supporting results, `f` has a
homotopy inverse; `SSet.HasHoInverse.ihomMap` transports it to
postcomposition, and `SSet.HasHoInverse.categoricalEquivalences`
concludes. No quasicategory hypothesis on the functor objects is
needed for the conclusion. -/
theorem categoricalEquivalences.ihomMap [Quasicategory X]
    [Quasicategory Y] (hf : categoricalEquivalences f) (K : SSet.{u}) :
    categoricalEquivalences ((ihom K).map f) :=
  (hf.hasHoInverse.ihomMap K).categoricalEquivalences

/-!
## The uniform finite-probe predicate
-/

/-- The uniform finite-probe shadow of full faithfulness on
mapping spaces: for every probe simplicial set `K`, the
postcomposition functor on ordinary homotopy categories
`h Fun(K, X) ⟶ h Fun(K, Y)` is full and faithful, i.e. bijective
on every hom-set (in the intended application
`K ∈ {Δ[m], ∂Δ[m], Δ[1] ⊗ Δ[m], …}` is finite and the vertices
and edges of `Fun(K, X)` represent the elements of all homotopy
groups of all right mapping spaces and their homotopies; see the
module header).

This predicate is only the fully-faithful half of an
equivalence of probe homotopy categories. It does **not**
include essential surjectivity of any probe functor (equivalence
would be full, faithful *and* essentially surjective): a fully
faithful functor need not be essentially surjective, e.g. the
inclusion of the one-object discrete category into the
two-object discrete category, and this predicate imposes no
condition on objects of `h Fun(K, Y)` outside the images of
hom-sets. In particular it is strictly weaker than requiring
each probe functor to be a `Functor.IsEquivalence`. Essential
surjectivity for categorical equivalences is recorded
separately by the stronger
`SSet.categoricalEquivalences.isEquivalence_mapHomotopyCategory_ihomMap`.
Compare `SSet.dwyerKanFullyFaithful`, the full mapping-space
statement, and `SSet.dwyerKanFullyFaithfulPiZero` from the supporting results, the analogous hom-set-bijectivity condition for
`SSet.mapHomotopyCategory f` itself (at vertices of `X`, not a
special case of the probe condition at any single `K`). Unlike
`SSet.dwyerKanFullyFaithful`, this predicate needs no Kan
hypotheses. -/
def dwyerKanFullyFaithfulProbes (f : X ⟶ Y) : Prop :=
  ∀ K : SSet.{u},
    (mapHomotopyCategory ((ihom K).map f)).Full ∧
      (mapHomotopyCategory ((ihom K).map f)).Faithful

/-- **A categorical equivalence between quasicategories is fully
faithful on all finite probes**: the uniform input for all
homotopy groups of all mapping spaces. This records only the
full-and-faithful part of the stronger equivalence
`SSet.categoricalEquivalences.isEquivalence_mapHomotopyCategory_ihomMap`
at every probe `K`. -/
theorem categoricalEquivalences.dwyerKanFullyFaithfulProbes
    [Quasicategory X] [Quasicategory Y]
    (hf : categoricalEquivalences f) :
    dwyerKanFullyFaithfulProbes f := by
  intro K
  have := hf.isEquivalence_mapHomotopyCategory_ihomMap K
  exact ⟨inferInstance, inferInstance⟩

/-- Functoriality of the probe functors on composites. -/
private lemma mapHomotopyCategory_ihomMap_comp' (K : SSet.{u})
    {f : X ⟶ Y} {g : Y ⟶ Z} :
    mapHomotopyCategory ((ihom K).map (f ≫ g)) =
      mapHomotopyCategory ((ihom K).map f) ⋙
        mapHomotopyCategory ((ihom K).map g) := by
  rw [(ihom K).map_comp]
  have hrw : ∀ {A B : SSet.{u}} (h : A ⟶ B),
      mapHomotopyCategory h = (hoFunctor.map h).toFunctor :=
    fun _ ↦ rfl
  rw [hrw, hrw, hrw, hoFunctor.map_comp]
  rfl

/-- The identity map satisfies the probe predicate, with no
quasicategory or Kan hypothesis: each probe functor is the
identity functor. -/
theorem dwyerKanFullyFaithfulProbes_id :
    dwyerKanFullyFaithfulProbes (𝟙 X) := by
  intro K
  have h1 : (ihom K).map (𝟙 X) = 𝟙 ((ihom K).obj X) :=
    (ihom K).map_id X
  rw [h1]
  change ((hoFunctor.map (𝟙 ((ihom K).obj X))).toFunctor).Full ∧
    ((hoFunctor.map (𝟙 ((ihom K).obj X))).toFunctor).Faithful
  rw [hoFunctor.map_id, Cat.Hom.id_toFunctor]
  exact ⟨inferInstance, inferInstance⟩

/-- The probe predicate is stable under composition, by
functoriality of postcomposition and of
`SSet.mapHomotopyCategory`. -/
theorem dwyerKanFullyFaithfulProbes.comp {g : Y ⟶ Z}
    (hf : dwyerKanFullyFaithfulProbes f)
    (hg : dwyerKanFullyFaithfulProbes g) :
    dwyerKanFullyFaithfulProbes (f ≫ g) := by
  intro K
  have hFullF : (mapHomotopyCategory ((ihom K).map f)).Full :=
    (hf K).1
  have hFaithF :
      (mapHomotopyCategory ((ihom K).map f)).Faithful := (hf K).2
  have hFullG : (mapHomotopyCategory ((ihom K).map g)).Full :=
    (hg K).1
  have hFaithG :
      (mapHomotopyCategory ((ihom K).map g)).Faithful := (hg K).2
  rw [mapHomotopyCategory_ihomMap_comp']
  exact ⟨inferInstance, inferInstance⟩

/-- **Two-out-of-six for the probe predicate** (the probe analogue
of the concluding step of Stevenson's Lemma 2.17, and of
`SSet.dwyerKanFullyFaithful.of_comp_comp`): if `f ≫ g` and
`g ≫ f` satisfy `SSet.dwyerKanFullyFaithfulProbes`, then `f`
does. Only fullness and faithfulness are involved: faithfulness
of the first probe functor cancels from `f ≫ g`, faithfulness
of the second cancels from `g ≫ f`, and fullness of the first
then follows from fullness of `f ≫ g` by
`Functor.Full.of_comp_faithful`. No essential surjectivity is
used or concluded. -/
theorem dwyerKanFullyFaithfulProbes.of_comp_comp {g : Y ⟶ X}
    (hfg : dwyerKanFullyFaithfulProbes (f ≫ g))
    (hgf : dwyerKanFullyFaithfulProbes (g ≫ f)) :
    dwyerKanFullyFaithfulProbes f := by
  intro K
  have hFGfull : ((mapHomotopyCategory ((ihom K).map f)) ⋙
      (mapHomotopyCategory ((ihom K).map g))).Full := by
    rw [← mapHomotopyCategory_ihomMap_comp']
    exact (hfg K).1
  have hFGfaith : ((mapHomotopyCategory ((ihom K).map f)) ⋙
      (mapHomotopyCategory ((ihom K).map g))).Faithful := by
    rw [← mapHomotopyCategory_ihomMap_comp']
    exact (hfg K).2
  have hGFfaith : ((mapHomotopyCategory ((ihom K).map g)) ⋙
      (mapHomotopyCategory ((ihom K).map f))).Faithful := by
    rw [← mapHomotopyCategory_ihomMap_comp']
    exact (hgf K).2
  have := hFGfull
  have := hFGfaith
  have := hGFfaith
  have hGfaith :
      (mapHomotopyCategory ((ihom K).map g)).Faithful :=
    Functor.Faithful.of_comp
      (mapHomotopyCategory ((ihom K).map g))
      (mapHomotopyCategory ((ihom K).map f))
  have := hGfaith
  exact ⟨Functor.Full.of_comp_faithful
      (mapHomotopyCategory ((ihom K).map f))
      (mapHomotopyCategory ((ihom K).map g)),
    Functor.Faithful.of_comp
      (mapHomotopyCategory ((ihom K).map f))
      (mapHomotopyCategory ((ihom K).map g))⟩

/-!
## Vertex-level consequences of the probe predicate
-/

/-- Each probe functor of a map satisfying
`SSet.dwyerKanFullyFaithfulProbes` is fully faithful (as a
`Functor.FullyFaithful` structure). -/
noncomputable def dwyerKanFullyFaithfulProbes.fullyFaithful
    (h : dwyerKanFullyFaithfulProbes f) (K : SSet.{u}) :
    (mapHomotopyCategory ((ihom K).map f)).FullyFaithful := by
  have := (h K).1
  have := (h K).2
  exact Functor.FullyFaithful.ofFullyFaithful _

/-- A map satisfying `SSet.dwyerKanFullyFaithfulProbes` induces
bijections on all morphism sets of probe homotopy categories. -/
theorem dwyerKanFullyFaithfulProbes.map_bijective
    (h : dwyerKanFullyFaithfulProbes f) (K : SSet.{u})
    (a b : ((ihom K).obj X).HomotopyCategory) :
    Function.Bijective
      ((mapHomotopyCategory ((ihom K).map f)).map :
        (a ⟶ b) →
          ((mapHomotopyCategory ((ihom K).map f)).obj a ⟶
            (mapHomotopyCategory ((ihom K).map f)).obj b)) :=
  (h.fullyFaithful K).map_bijective a b

/-- The morphism represented by an edge transported along
endpoint equalities is the conjugate of the represented morphism
by the corresponding `eqToHom` maps. -/
private lemma homMk_ofEq' {A : SSet.{u}} {x₀ x₁ y₀ y₁ : A _⦋0⦌}
    (e : Edge x₀ x₁) (h₀ : x₀ = y₀) (h₁ : x₁ = y₁) :
    HomotopyCategory.homMk (e.ofEq h₀ h₁) =
      eqToHom (congrArg HomotopyCategory.mk h₀).symm ≫
        HomotopyCategory.homMk e ≫
        eqToHom (congrArg HomotopyCategory.mk h₁) := by
  cases h₀
  cases h₁
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  congr 1

/-- The object formula for a probe functor at a classified
vertex: postcomposition sends the vertex classified by `u` to
the vertex classified by `u ≫ f`. -/
lemma mapHomotopyCategory_ihomMap_obj_mk_ihomVertexEquiv
    (K : SSet.{u}) (u : K ⟶ X) :
    (mapHomotopyCategory ((ihom K).map f)).obj
        (HomotopyCategory.mk (ihomVertexEquiv K X u)) =
      HomotopyCategory.mk (ihomVertexEquiv K Y (u ≫ f)) := by
  rw [mapHomotopyCategory_obj_mk, ihomVertexEquiv_ihom_map]

/-- The morphism-set equivalence induced by a map satisfying
`SSet.dwyerKanFullyFaithfulProbes` at a pair of vertices of
`Fun(K, X)` classified by maps `u v : K ⟶ X`. For `K = Δ[m]` the
vertices are `m`-simplices (by Yoneda) and these morphism sets
are the representing edge sets for mapping-space homotopy
groups; see the module header. -/
noncomputable def dwyerKanFullyFaithfulProbes.homEquivMk
    (h : dwyerKanFullyFaithfulProbes f) (K : SSet.{u}) (u v : K ⟶ X) :
    (HomotopyCategory.mk (ihomVertexEquiv K X u) ⟶
        HomotopyCategory.mk (ihomVertexEquiv K X v)) ≃
      (HomotopyCategory.mk (ihomVertexEquiv K Y (u ≫ f)) ⟶
        HomotopyCategory.mk (ihomVertexEquiv K Y (v ≫ f))) :=
  (h.fullyFaithful K).homEquiv.trans
    (Iso.homCongr
      (eqToIso (mapHomotopyCategory_ihomMap_obj_mk_ihomVertexEquiv K u))
      (eqToIso (mapHomotopyCategory_ihomMap_obj_mk_ihomVertexEquiv K v)))

/-- Compatibility name for the equivalence on classified probe vertices.
The deprecated public spelling retains its original underscore. -/
@[deprecated dwyerKanFullyFaithfulProbes.homEquivMk (since := "2026-11-03"),
  nolint defsWithUnderscore]
alias dwyerKanFullyFaithfulProbes.homEquiv_mk := dwyerKanFullyFaithfulProbes.homEquivMk

/-- The equivalence `SSet.dwyerKanFullyFaithfulProbes.homEquivMk`
sends the class of an edge of `Fun(K, X)` to the class of its
image edge under postcomposition, transported along the
canonical endpoint identifications
`SSet.ihomVertexEquiv_ihom_map`. -/
theorem dwyerKanFullyFaithfulProbes.homEquiv_mk_toHoHom
    (h : dwyerKanFullyFaithfulProbes f) (K : SSet.{u}) {u v : K ⟶ X}
    (e : Edge (ihomVertexEquiv K X u) (ihomVertexEquiv K X v)) :
    h.homEquivMk K u v e.toHoHom =
      ((e.map ((ihom K).map f)).ofEq (ihomVertexEquiv_ihom_map u f)
        (ihomVertexEquiv_ihom_map v f)).toHoHom := by
  have hu' : mapHomotopyCategory_ihomMap_obj_mk_ihomVertexEquiv K u =
      congrArg HomotopyCategory.mk (ihomVertexEquiv_ihom_map u f) :=
    proof_irrel _ _
  have hv' : mapHomotopyCategory_ihomMap_obj_mk_ihomVertexEquiv K v =
      congrArg HomotopyCategory.mk (ihomVertexEquiv_ihom_map v f) :=
    proof_irrel _ _
  simp only [Edge.toHoHom_eq_homMk]
  rw [dwyerKanFullyFaithfulProbes.homEquivMk, Equiv.trans_apply,
    Functor.FullyFaithful.homEquiv_apply, Iso.homCongr_apply,
    mapHomotopyCategory_map_homMk, homMk_ofEq', eqToIso.inv,
    eqToIso.hom, hu', hv']
  rfl

/-- **Fullness on representing edges**: if `f` satisfies
`SSet.dwyerKanFullyFaithfulProbes` and `X` is a quasicategory
(so that morphisms of `h Fun(K, X)` are represented by single
edges), then every edge of `Fun(K, Y)` between image vertices is
homotopic to the image of an edge of `Fun(K, X)`. -/
theorem dwyerKanFullyFaithfulProbes.exists_edge_map_ofEq_toHoHom_eq
    [Quasicategory X] (h : dwyerKanFullyFaithfulProbes f)
    (K : SSet.{u}) {u v : K ⟶ X}
    (e' : Edge (ihomVertexEquiv K Y (u ≫ f))
      (ihomVertexEquiv K Y (v ≫ f))) :
    ∃ e : Edge (ihomVertexEquiv K X u) (ihomVertexEquiv K X v),
      ((e.map ((ihom K).map f)).ofEq (ihomVertexEquiv_ihom_map u f)
        (ihomVertexEquiv_ihom_map v f)).toHoHom = e'.toHoHom := by
  obtain ⟨ξ, hξ⟩ := (h.homEquivMk K u v).surjective e'.toHoHom
  obtain ⟨e, rfl⟩ := Edge.exists_toHoHom_eq ξ
  exact ⟨e, by rw [← h.homEquiv_mk_toHoHom]; exact hξ⟩

/-- **Faithfulness on representing edges**: if `f` satisfies
`SSet.dwyerKanFullyFaithfulProbes` and two edges of `Fun(K, X)`
have homotopic images in `Fun(K, Y)`, then they are homotopic in
`Fun(K, X)`. -/
theorem dwyerKanFullyFaithfulProbes.edge_map_ofEq_toHoHom_injective
    (h : dwyerKanFullyFaithfulProbes f) (K : SSet.{u}) {u v : K ⟶ X}
    {e₁ e₂ : Edge (ihomVertexEquiv K X u) (ihomVertexEquiv K X v)}
    (hh : ((e₁.map ((ihom K).map f)).ofEq (ihomVertexEquiv_ihom_map u f)
        (ihomVertexEquiv_ihom_map v f)).toHoHom =
      ((e₂.map ((ihom K).map f)).ofEq (ihomVertexEquiv_ihom_map u f)
        (ihomVertexEquiv_ihom_map v f)).toHoHom) :
    e₁.toHoHom = e₂.toHoHom := by
  rw [← h.homEquiv_mk_toHoHom, ← h.homEquiv_mk_toHoHom] at hh
  exact (h.homEquivMk K u v).injective hh

/-!
## Whitehead assembly for mapping spaces
-/

/-- The pointwise Whitehead criterion: Kan right mapping spaces and
bijections on their connected components and every positive based homotopy
group imply mapping-space full faithfulness. This generic assembly retains
all four supplied hypotheses. For quasicategories, the unconditional
same-map theorem is `categoricalEquivalences.rightMappingSpaceMap_weak`
in the downstream `RightMappingBrown.lean` module. -/
theorem dwyerKanFullyFaithful.of_kan_bijective_mapPiZero_piMap
    (hKanX : ∀ a b : (Δ[0] : SSet.{u}) ⟶ X,
      KanComplex (mappingSpaceRight X a b))
    (hKanY : ∀ a b : (Δ[0] : SSet.{u}) ⟶ X,
      KanComplex (mappingSpaceRight Y (a ≫ f) (b ≫ f)))
    (h₀ : ∀ a b : (Δ[0] : SSet.{u}) ⟶ X,
      Function.Bijective (mapπ₀ (mappingSpaceRight.map X a b f)))
    (hπ : ∀ (a b : (Δ[0] : SSet.{u}) ⟶ X) (n : ℕ)
      (σ : (mappingSpaceRight X a b) _⦋0⦌),
      Function.Bijective
        (KanComplex.π.map (mappingSpaceRight.map X a b f) rfl
          (n := n + 1) (x := σ))) :
    dwyerKanFullyFaithful f :=
  dwyerKanFullyFaithful.of_kanComplexW hKanX hKanY
    (fun a b => (KanComplex.W_iff _).2 ⟨h₀ a b, fun n σ ↦ hπ a b n σ⟩)

/-- Combine categorical essential surjectivity with the explicit
pointwise Whitehead hypotheses to obtain a Dwyer–Kan equivalence. The
unconditional theorem for quasicategories is supplied downstream by
`categoricalEquivalences.isDwyerKanEquivalence`; this general lemma keeps
its original Kan and homotopy-group assumptions. -/
theorem
    categoricalEquivalences.isDwyerKanEquivalence_of_kan_bijective_mapPiZero_piMap
    (hf : categoricalEquivalences f)
    (hKanX : ∀ a b : (Δ[0] : SSet.{u}) ⟶ X,
      KanComplex (mappingSpaceRight X a b))
    (hKanY : ∀ a b : (Δ[0] : SSet.{u}) ⟶ X,
      KanComplex (mappingSpaceRight Y (a ≫ f) (b ≫ f)))
    (h₀ : ∀ a b : (Δ[0] : SSet.{u}) ⟶ X,
      Function.Bijective (mapπ₀ (mappingSpaceRight.map X a b f)))
    (hπ : ∀ (a b : (Δ[0] : SSet.{u}) ⟶ X) (n : ℕ)
      (σ : (mappingSpaceRight X a b) _⦋0⦌),
      Function.Bijective
        (KanComplex.π.map (mappingSpaceRight.map X a b f) rfl
          (n := n + 1) (x := σ))) :
    isDwyerKanEquivalence f :=
  ⟨hf.dwyerKanEssentiallySurjective,
    dwyerKanFullyFaithful.of_kan_bijective_mapPiZero_piMap hKanX hKanY
      h₀ hπ⟩

end SSet

end
