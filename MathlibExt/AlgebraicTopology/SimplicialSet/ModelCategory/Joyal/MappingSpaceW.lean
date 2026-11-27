/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.MappingSpaceCategorical
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FundamentalGroupoidPiOne
public import MathlibExt.AlgebraicTopology.Quasicategory.CategoricalProbes

/-!
# Postcomposition probes and mapping-space weak equivalences

For simplicial sets K,X in universe u, internal postcomposition sends an endomorphism φ:X→X to
the endomorphism (−≫φ) of X^K. It preserves the two inverse-isomorphism witnesses of a homotopy
inverse. For quasicategories X,Y, categorical f:X→Y therefore gives categorical X^K→Y^K for
every K.

For f:X→Y in universe u and a simplicial probe K in the same universe, write T_K:ho(X^K)→ho(Y^K)
for postcomposition by f. The probe full-faithfulness condition says that T_K is full and
faithful for every K, hence bijective on each hom-set. It is stable under identities,
composition and the two reverse composites f≫g,g≫f. It gives explicit hom-set equivalences and
edge-class lifting for quasicategory source X.

Right mapping-space full faithfulness is also assembled from Kan source and target mapping
spaces, connected-component bijectivity, and positive based homotopy-group bijectivity. All of
these stated inputs belong to that criterion.

References: D. Stevenson, Notes on the Joyal model structure, arXiv:1810.05233; J. Lurie, Higher
Topos Theory, §1.2.2.
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

The map X^X→(X^K)^(X^K) is the curry of internal composition. On vertices it sends φ:X→X to
postcomposition by φ on X^K.
-/

/-- For K,X in simplicial-set universe u, define P:X^X→(X^K)^(X^K) by currying internal composition
X^K⊗X^X→X^K. At a vertex φ:X→X it represents the endomorphism α↦α≫φ of X^K. -/
noncomputable def ihomPostcompositionMap (K X : SSet.{u}) :
    (ihom X).obj X ⟶ (ihom ((ihom K).obj X)).obj ((ihom K).obj X) :=
  MonoidalClosed.curry (MonoidalClosed.comp K X X)

/-- For K,X in universe u, the uncurry of P:X^X→(X^K)^(X^K) is internal composition X^K⊗X^X→X^K. -/
lemma uncurry_ihomPostcompositionMap (K X : SSet.{u}) :
    MonoidalClosed.uncurry (ihomPostcompositionMap K X) =
      MonoidalClosed.comp K X X := by
  simp only [ihomPostcompositionMap, MonoidalClosed.uncurry_curry]

/-- For K,X in universe u and φ:X→X, the curried name of φ followed by P:X^X→(X^K)^(X^K) equals the
curried name of the map X^K→X^K given by postcomposition with φ. -/
lemma curry'_comp_ihomPostcompositionMap (K X : SSet.{u}) (φ : X ⟶ X) :
    MonoidalClosed.curry' φ ≫ ihomPostcompositionMap K X =
      MonoidalClosed.curry' ((ihom K).map φ) := by
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left, uncurry_ihomPostcompositionMap,
    MonoidalClosed.whiskerLeft_curry'_comp]
  simp [MonoidalClosed.curry']

/-- For K,X in universe u and φ:X→X, P sends the vertex [φ] of X^X to the vertex of (X^K)^(X^K)
classified by (−≫φ):X^K→X^K. -/
lemma ihomPostcompositionMap_app_ihomVertexEquiv (K X : SSet.{u})
    (φ : X ⟶ X) :
    (ihomPostcompositionMap K X).app (op ⦋0⦌) (ihomVertexEquiv X X φ) =
      ihomVertexEquiv ((ihom K).obj X) ((ihom K).obj X) ((ihom K).map φ) :=
  congrArg (fun ψ : 𝟙_ SSet.{u} ⟶
      (ihom ((ihom K).obj X)).obj ((ihom K).obj X) => ψ.app _ PUnit.unit)
    (curry'_comp_ihomPostcompositionMap K X φ)

/-!
## Object formulas for the homotopy-category functor

A map θ:A→B induces [v]↦[θ(v)] on vertex objects of ho(A)→ho(B). Applied to internal
postcomposition, this transports homotopy-inverse isomorphisms to all probes K.
-/

/-- For θ:A→B of simplicial sets in universe u and v∈A₀, ho(θ)([v])=[θ₀(v)] as objects of ho(B). -/
private lemma hoFunctor_map_obj_mk' {A B : SSet.{u}} (θ : A ⟶ B)
    (v : A _⦋0⦌) :
    (hoFunctor.map θ).toFunctor.obj (HomotopyCategory.mk v) =
      HomotopyCategory.mk (θ.app _ v) :=
  mapHomotopyCategory_obj_mk θ v

/-- For f:X→Y in universe u with a reverse map g:Y→X and inverse isomorphisms [f≫g]≅[id_X],
[g≫f]≅[id_Y] in the corresponding internal-hom homotopy categories, every K gives a homotopy
inverse for X^K→Y^K, with reverse map postcomposition by g. -/
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

/-- For f:X→Y of simplicial sets in universe u, categorical equivalence means that precomposition
gives an equivalence ho(Q^Y)→ho(Q^X) for every quasicategory Q in that universe. If X,Y are
quasicategories, then postcomposition X^K→Y^K is categorical for every simplicial set K in
universe u. -/
theorem categoricalEquivalences.ihomMap [Quasicategory X]
    [Quasicategory Y] (hf : categoricalEquivalences f) (K : SSet.{u}) :
    categoricalEquivalences ((ihom K).map f) :=
  (hf.hasHoInverse.ihomMap K).categoricalEquivalences

/-!
## Full faithfulness for every probe

For each simplicial K, T_K is required to be full and faithful on homotopy-category morphisms.
The probe K is arbitrary; identity and composite maps satisfy the corresponding closure laws.
-/

/-- For f:X→Y in universe u and a simplicial probe K in the same universe, write T_K:ho(X^K)→ho(Y^K)
for postcomposition by f. The probe full-faithfulness condition says that T_K is full and
faithful for every K, hence bijective on each hom-set. Thus for any objects a,b of ho(X^K), T_K
induces a bijection Hom(a,b)→Hom(T_Ka,T_Kb). -/
def dwyerKanFullyFaithfulProbes (f : X ⟶ Y) : Prop :=
  ∀ K : SSet.{u},
    (mapHomotopyCategory ((ihom K).map f)).Full ∧
      (mapHomotopyCategory ((ihom K).map f)).Faithful

/-- For f:X→Y of simplicial sets in universe u, categorical equivalence means that precomposition
gives an equivalence ho(Q^Y)→ho(Q^X) for every quasicategory Q in that universe. If X,Y are
quasicategories, every postcomposition functor T_K:ho(X^K)→ho(Y^K) is full and faithful. -/
theorem categoricalEquivalences.dwyerKanFullyFaithfulProbes
    [Quasicategory X] [Quasicategory Y]
    (hf : categoricalEquivalences f) :
    dwyerKanFullyFaithfulProbes f := by
  intro K
  have := hf.isEquivalence_mapHomotopyCategory_ihomMap K
  exact ⟨inferInstance, inferInstance⟩

/-- For K in universe u and f:X→Y, g:Y→Z, postcomposition T_K(f≫g):ho(X^K)→ho(Z^K) equals
T_K(f)⋙T_K(g). -/
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

/-- For any simplicial set X in universe u and every K, postcomposition by id_X induces the identity
functor of ho(X^K), hence is full and faithful. -/
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

/-- For f:X→Y and g:Y→Z in universe u, if T_K(f) and T_K(g) are full and faithful for every K, then
T_K(f≫g) is full and faithful for every K. -/
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

/-- For f:X→Y and g:Y→X in universe u, if all probe functors of f≫g and of g≫f are full and
faithful, then every T_K(f):ho(X^K)→ho(Y^K) is full and faithful. -/
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
## Equivalences on probe hom-sets

Probe full faithfulness gives equivalences ho(X^K)([α],[β])≃ho(Y^K)([α≫f],[β≫f]) for α,β:K→X.
Forward images of edge classes use the canonical endpoint identifications of postcomposition.
-/

/-- For f:X→Y in universe u and a simplicial probe K in the same universe, write T_K:ho(X^K)→ho(Y^K)
for postcomposition by f. If f satisfies full faithfulness for every probe, this supplies a
full-and-faithful structure on T_K for each K. -/
noncomputable def dwyerKanFullyFaithfulProbes.fullyFaithful
    (h : dwyerKanFullyFaithfulProbes f) (K : SSet.{u}) :
    (mapHomotopyCategory ((ihom K).map f)).FullyFaithful := by
  have := (h K).1
  have := (h K).2
  exact Functor.FullyFaithful.ofFullyFaithful _

/-- For f:X→Y in universe u and a simplicial probe K in the same universe, write T_K:ho(X^K)→ho(Y^K)
for postcomposition by f. Suppose f satisfies probe full faithfulness. For any a,b in ho(X^K),
the map Hom(a,b)→Hom(T_Ka,T_Kb) is bijective. -/
theorem dwyerKanFullyFaithfulProbes.map_bijective
    (h : dwyerKanFullyFaithfulProbes f) (K : SSet.{u})
    (a b : ((ihom K).obj X).HomotopyCategory) :
    Function.Bijective
      ((mapHomotopyCategory ((ihom K).map f)).map :
        (a ⟶ b) →
          ((mapHomotopyCategory ((ihom K).map f)).obj a ⟶
            (mapHomotopyCategory ((ihom K).map f)).obj b)) :=
  (h.fullyFaithful K).map_bijective a b

/-- For A in universe u, an edge e:x₀→x₁ and vertex equalities h₀:x₀=y₀, h₁:x₁=y₁, the transported
edge y₀→y₁ represents eq(h₀)⁻¹≫[e]≫eq(h₁) in ho(A). Here eq(hᵢ) is the identity transport
between the corresponding vertex objects. -/
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

/-- For f:X→Y, a probe K and α:K→X in universe u, T_K sends the vertex object [α] of ho(X^K) to
[α≫f] in ho(Y^K). -/
lemma mapHomotopyCategory_ihomMap_obj_mk_ihomVertexEquiv
    (K : SSet.{u}) (u : K ⟶ X) :
    (mapHomotopyCategory ((ihom K).map f)).obj
        (HomotopyCategory.mk (ihomVertexEquiv K X u)) =
      HomotopyCategory.mk (ihomVertexEquiv K Y (u ≫ f)) := by
  rw [mapHomotopyCategory_obj_mk, ihomVertexEquiv_ihom_map]

/-- For f:X→Y in universe u and a simplicial probe K in the same universe, write T_K:ho(X^K)→ho(Y^K)
for postcomposition by f. If all probe functors are full and faithful, then for α,β:K→X, T_K
gives an equivalence Hom_{ho(X^K)}([α],[β])≃Hom_{ho(Y^K)}([α≫f],[β≫f]). -/
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

/-- For f:X→Y in universe u and a simplicial probe K in the same universe, write T_K:ho(X^K)→ho(Y^K)
for postcomposition by f. Under probe full faithfulness, the represented vertex hom-sets
Hom([α],[β]) and Hom([α≫f],[β≫f]) are equivalent for all α,β:K→X, with forward map T_K on
morphisms. -/
@[deprecated dwyerKanFullyFaithfulProbes.homEquivMk (since := "2026-11-03"),
  nolint defsWithUnderscore]
alias dwyerKanFullyFaithfulProbes.homEquiv_mk := dwyerKanFullyFaithfulProbes.homEquivMk

/-- For f:X→Y in universe u and a simplicial probe K in the same universe, write T_K:ho(X^K)→ho(Y^K)
for postcomposition by f. Under probe full faithfulness, an edge e:[α]→[β] of X^K is sent by the
represented hom-set equivalence to the class of its image under X^K→Y^K, after identifying the
image vertices with [α≫f] and [β≫f]. -/
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

/-- For f:X→Y in universe u and a simplicial probe K in the same universe, write T_K:ho(X^K)→ho(Y^K)
for postcomposition by f. Suppose all T_K are full and faithful and X is a quasicategory. For
α,β:K→X and a target edge e′:[α≫f]→[β≫f] in Y^K, there is e:[α]→[β] in X^K whose transported
image represents the same morphism as e′ in ho(Y^K). -/
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

/-- For f:X→Y in universe u and a simplicial probe K in the same universe, write T_K:ho(X^K)→ho(Y^K)
for postcomposition by f. Under probe full faithfulness, if two edges [α]→[β] in X^K have equal
postcomposition classes after the canonical target endpoint identifications, their classes in
ho(X^K) are equal. -/
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
## The pointwise Kan criterion

For every pair a,b:Δ[0]→X, suppose R_X(a,b) and R_Y(a≫f,b≫f) are Kan. Bijectivity on their
connected components and all positive π_n at each source basepoint makes the realized right
mapping-space map a weak homotopy equivalence.
-/

/-- For f:X→Y in universe u, For vertex maps a,b:Δ[0]→X, write r_{a,b}:R_X(a,b)→R_Y(a≫f,b≫f) for the
induced map of right mapping spaces. Suppose every source and target right mapping space is Kan,
r_{a,b} is bijective on connected components, and for every source vertex σ and n∈ℕ it induces a
bijection on π_{n+1} based at σ and r_{a,b}(σ). Then each |r_{a,b}| is a weak homotopy
equivalence, so f is Dwyer–Kan fully faithful. -/
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

/-- For f:X→Y of simplicial sets in universe u, categorical equivalence means that precomposition
gives an equivalence ho(Q^Y)→ho(Q^X) for every quasicategory Q in that universe. For vertex maps
a,b:Δ[0]→X, write r_{a,b}:R_X(a,b)→R_Y(a≫f,b≫f) for the induced map of right mapping spaces. If
all these source and target mapping spaces are Kan, all r_{a,b} are bijective on connected
components, and every positive based π_{n+1} map at every source vertex is bijective, then f is
a Dwyer–Kan equivalence. -/
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
