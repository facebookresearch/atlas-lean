/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction
public import MathlibExt.AlgebraicTopology.SimplicialSet.IhomVertices

/-! # Descent of maps into nerves

Generic nerve-descent infrastructure for simplicial sets, deliberately
placed below the Joyal model-structure theory. It contains:

* descent of a map `g : Z ⟶ nerve D` to a functor
  `Z.HomotopyCategory ⥤ D` (`SSet.descNerve`), with object,
  generating-morphism, precomposition, and postcomposition formulas;
* detection of maps into nerves on `2`-truncations
  (`SSet.nerveTruncEquiv`, `SSet.nerveTruncEquiv_apply`) and
  injectivity of descent (`SSet.descNerve_injective`);
* the identification of descent with transposition across
  `CategoryTheory.nerveAdjunction`
  (`SSet.nerveAdjunction_homEquiv_symm_apply`), together with the
  descent and `2`-truncation formulas for the canonical adjunction
  unit and the counit (`SSet.nerveAdjunction_counit_app_toFunctor`);
* evaluation of maps and edges in functor objects into nerves at a
  vertex (`SSet.eval_app_pre_app_ihomVertexEquiv`,
  `SSet.edgeAtVertex`).

## Universes

The descent, detection, and evaluation API is universe-general: the
target category is `D : Type u` with `[Category.{v} D]` for
independent object and morphism universes `u` and `v`, and the source
simplicial set lies in `SSet.{max u v}`, the universe of
`CategoryTheory.nerve D`. Upstream
`SSet.Truncated.HomotopyCategory.descOfTruncation` is restricted to
small categories (`D : Type u`, `Category.{u} D`), so the truncated
descent used here is a universe-general form of it. The
adjunction results are isolated in their own section at a single
universe `s`, because `CategoryTheory.nerveAdjunction` and
`Cat.{s, s}` force the object and morphism universes to agree there.

This module imports only upstream nerve/homotopy-category API and
`MathlibExt.AlgebraicTopology.SimplicialSet.IhomVertices`; in
particular it knows nothing about Joyal categorical equivalences.
Joyal modules import it for their nerve characterizations.

## References

* J. Lurie, *Higher Topos Theory*, §2.3.
* D. Stevenson, *Notes on the Joyal model structure*, arXiv:1810.05233.
-/

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory MonoidalClosed Limits Opposite
open SimplexCategory.Truncated SimplicialObject.Truncated

open scoped Simplicial

universe v u s

namespace SSet

variable {V : SSet.Truncated.{max u v} 2} {D E : Type u}
variable [Category.{v} D] [Category.{v} E]
variable {Z Y : SSet.{max u v}}

/-! ## Truncated descent (universe-general form of upstream descent) -/

/-- Descent of a map from a `2`-truncated simplicial set into a
truncated nerve to a functor on homotopy categories. This is the
universe-general form of upstream
`SSet.Truncated.HomotopyCategory.descOfTruncation` (which requires a
small target category); the definition is the same
`Truncated.HomotopyCategory.lift`. At a single universe it agrees
with the upstream definition (`descOfTruncation_eq_upstream` below). -/
def descOfTruncation
    (φ : V ⟶ (truncation 2).obj (CategoryTheory.nerve D)) :
    V.HomotopyCategory ⥤ D :=
  Truncated.HomotopyCategory.lift (fun x ↦ CategoryTheory.nerveEquiv (φ.app _ x))
    (fun e ↦ CategoryTheory.nerve.homEquiv (e.map φ))
    (fun x ↦ by simpa using! CategoryTheory.nerve.homEquiv_id (φ.app _ x))
    (fun h ↦ CategoryTheory.nerve.homEquiv_comp (h.map φ))

@[simp]
lemma descOfTruncation_obj_mk
    (φ : V ⟶ (truncation 2).obj (CategoryTheory.nerve D)) (x : V _⦋0⦌₂) :
    (descOfTruncation φ).obj (Truncated.HomotopyCategory.mk x) =
      CategoryTheory.nerveEquiv (φ.app _ x) := rfl

@[simp]
lemma descOfTruncation_map_homMk
    (φ : V ⟶ (truncation 2).obj (CategoryTheory.nerve D))
    {x₀ x₁ : V _⦋0⦌₂} (e : Truncated.Edge x₀ x₁) :
    (descOfTruncation φ).map (Truncated.HomotopyCategory.homMk e) =
      CategoryTheory.nerve.homEquiv (e.map φ) :=
  Category.id_comp _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
lemma descOfTruncation_comp {W : SSet.Truncated.{max u v} 2}
    (ψ : V ⟶ W) (φ : W ⟶ (truncation 2).obj (CategoryTheory.nerve D)) :
    descOfTruncation (ψ ≫ φ) =
      Truncated.mapHomotopyCategory ψ ⋙ descOfTruncation φ :=
  Truncated.HomotopyCategory.functor_ext (fun _ ↦ by simp) (by cat_disch)

/-- `nerveEquiv` of a `nerveMap`-image `0`-simplex (definitional). -/
private lemma nerveEquiv_nerveMap_app (K : D ⥤ E)
    (t : ((truncation 2).obj (CategoryTheory.nerve D)) _⦋0⦌₂) :
    CategoryTheory.nerveEquiv
        (((truncation 2).map (CategoryTheory.nerveMap K)).app _ t) =
      K.obj (CategoryTheory.nerveEquiv t) := rfl

/-- `nerve.homEquiv` commutes with mapping an edge along `nerveMap K`:
the general-edge form of upstream
`CategoryTheory.nerve.homEquiv_edgeMk_map_nerveMap`, by reduction to
`edgeMk`. -/
private lemma nerve_homEquiv_map_nerveMap (K : D ⥤ E)
    {x y : CategoryTheory.ComposableArrows D 0}
    (e : (CategoryTheory.nerve D).Edge x y) :
    CategoryTheory.nerve.homEquiv (e.map (CategoryTheory.nerveMap K)) =
      K.map (CategoryTheory.nerve.homEquiv e) := by
  obtain ⟨x, rfl⟩ := CategoryTheory.nerveEquiv.symm.surjective x
  obtain ⟨y, rfl⟩ := CategoryTheory.nerveEquiv.symm.surjective y
  obtain ⟨f, rfl⟩ := CategoryTheory.nerve.edgeMk_surjective e
  rw [CategoryTheory.nerve.homEquiv_edgeMk]
  exact CategoryTheory.nerve.homEquiv_edgeMk_map_nerveMap f K

/-- Truncated form of `nerve_homEquiv_map_nerveMap` (definitionally the
same statement, stated so that rewriting matches truncated-edge
goals). -/
private lemma nerve_homEquiv_map_truncationMap_nerveMap (K : D ⥤ E)
    {x y : ((truncation 2).obj (CategoryTheory.nerve D)) _⦋0⦌₂}
    (t : ((truncation 2).obj (CategoryTheory.nerve D)).Edge x y) :
    CategoryTheory.nerve.homEquiv
        (t.map ((truncation 2).map (CategoryTheory.nerveMap K))) =
      K.map (CategoryTheory.nerve.homEquiv t) :=
  nerve_homEquiv_map_nerveMap K (Edge.ofTruncated t)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Universe-general postcomposition of truncated descent with a
functor, through `nerveMap`. Upstream `nerveMap` forces `D` and `E` to
share the universe pair `(u, v)`, but `u ≠ v` is allowed. The object
comparison is definitional (`nerveEquiv_nerveMap_app`), so the
`eqToHom` conjugations in `functor_ext` are handled by
`conj_eqToHom_iff_heq`. -/
lemma descOfTruncation_comp_nerveMap
    (φ : V ⟶ (truncation 2).obj (CategoryTheory.nerve D)) (K : D ⥤ E) :
    descOfTruncation (φ ≫ (truncation 2).map (CategoryTheory.nerveMap K)) =
      descOfTruncation φ ⋙ K := by
  refine Truncated.HomotopyCategory.functor_ext
    (fun _ ↦ by simp [nerveEquiv_nerveMap_app]) ?_
  intro x y e
  simp only [descOfTruncation_map_homMk, Functor.comp_map]
  refine (CategoryTheory.conj_eqToHom_iff_heq _ _
    (by simp [nerveEquiv_nerveMap_app])
    (by simp [nerveEquiv_nerveMap_app])).mpr ?_
  have hEq : CategoryTheory.nerve.homEquiv
        (e.map (φ ≫ (truncation 2).map (CategoryTheory.nerveMap K))) =
      K.map (CategoryTheory.nerve.homEquiv (e.map φ)) :=
    nerve_homEquiv_map_truncationMap_nerveMap K (e.map φ)
  exact Eq.ndrec (motive := fun x ↦ HEq _ x) (HEq.refl _) hEq

/-! ## Descent of maps into nerves to homotopy categories -/

/-- **Descent of a map into a nerve.** For `g : Z ⟶ nerve D`, its
descent `SSet.descNerve g : Z.HomotopyCategory ⥤ D` is the functor
sending a vertex `z` to `CategoryTheory.nerveEquiv (g.app _ z)` and a
generating morphism `SSet.HomotopyCategory.homMk e` to
`CategoryTheory.nerve.homEquiv (e.map g)`. -/
def descNerve (g : Z ⟶ CategoryTheory.nerve D) : Z.HomotopyCategory ⥤ D :=
  descOfTruncation ((truncation 2).map g)

/-- Descent on objects: the class of a vertex maps to the vertex's
image read off through `nerveEquiv`. -/
@[simp]
theorem descNerve_obj_mk (g : Z ⟶ CategoryTheory.nerve D) (z : Z _⦋0⦌) :
    (descNerve g).obj (HomotopyCategory.mk z) =
      CategoryTheory.nerveEquiv (g.app (op ⦋0⦌) z) := by
  change (descOfTruncation ((truncation 2).map g)).obj (HomotopyCategory.mk z) = _
  rfl

/-- Descent on generating morphisms: the class of an edge maps to the
morphism classified by its image edge. -/
@[simp]
theorem descNerve_map_homMk (g : Z ⟶ CategoryTheory.nerve D)
    {x y : Z _⦋0⦌} (e : Edge x y) :
    (descNerve g).map (HomotopyCategory.homMk e) =
      CategoryTheory.nerve.homEquiv (e.map g) := by
  change (descOfTruncation ((truncation 2).map g)).map (HomotopyCategory.homMk e) = _
  exact descOfTruncation_map_homMk _ e.toTruncated

/-- Descent precomposed with a simplicial map is precomposition on
homotopy categories followed by descent. -/
theorem descNerve_precomp (f : Z ⟶ Y) (g : Y ⟶ CategoryTheory.nerve D) :
    descNerve (f ≫ g) = mapHomotopyCategory f ⋙ descNerve g := by
  rw [descNerve, descNerve, Functor.map_comp]
  exact descOfTruncation_comp _ _

/-- Descent postcomposed with a nerve map is descent followed by the
functor. -/
theorem descNerve_postcomp_nerveMap (g : Z ⟶ CategoryTheory.nerve D) (K : D ⥤ E) :
    descNerve (g ≫ CategoryTheory.nerveMap K) = descNerve g ⋙ K := by
  change descOfTruncation ((truncation 2).map (g ≫ CategoryTheory.nerveMap K)) =
    descOfTruncation ((truncation 2).map g) ⋙ K
  rw [Functor.map_comp]
  exact descOfTruncation_comp_nerveMap _ K

/-- Maps from `Z` into a nerve are detected on `2`-truncations, by
`2`-coskeletality of nerves. -/
def nerveTruncEquiv (Z : SSet.{max u v}) (D : Type u) [Category.{v} D] :
    (Z ⟶ CategoryTheory.nerve D) ≃
      ((truncation 2).obj Z ⟶ (truncation 2).obj (CategoryTheory.nerve D)) :=
  ((CategoryTheory.Nerve.cosk₂Iso.app (Cat.of D)).homToEquiv).trans
    ((coskAdj 2).homEquiv Z
      ((truncation 2).obj (CategoryTheory.nerve D))).symm

theorem nerveTruncEquiv_apply (φ : Z ⟶ CategoryTheory.nerve D) :
    nerveTruncEquiv Z D φ = (truncation 2).map φ := by
  change (truncation 2).map (φ ≫ (coskAdj 2).unit.app (CategoryTheory.nerve D)) ≫
      (coskAdj 2).counit.app ((truncation 2).obj (CategoryTheory.nerve D)) =
    (truncation 2).map φ
  rw [Functor.map_comp, Category.assoc,
    (coskAdj 2).left_triangle_components, Category.comp_id]

private theorem eq_of_truncation_map_eq {a b : Z ⟶ CategoryTheory.nerve D}
    (h : (truncation 2).map a = (truncation 2).map b) : a = b :=
  (nerveTruncEquiv Z D).injective (by rw [nerveTruncEquiv_apply,
    nerveTruncEquiv_apply, h])

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- **Descent is injective**: two maps into a nerve with equal
descents agree. Direct `IsStrictSegal.hom_ext` proof: a `1`-simplex
of a nerve is `mk₁` of the morphism read off by
`CategoryTheory.nerve.homEquiv`, that morphism is the descent on the
corresponding generating morphism, and equality of the descents as
*arrows* is extracted without transports through `Functor.mapArrow`
(the same device upstream uses in `homToNerveMk`). -/
theorem descNerve_injective :
    Function.Injective (fun g : Z ⟶ CategoryTheory.nerve D => descNerve g) := by
  intro a b hab
  apply eq_of_truncation_map_eq
  apply Truncated.IsStrictSegal.hom_ext
  intro s
  obtain ⟨x₀, x₁, f, hf⟩ := Truncated.Edge.exists_of_simplex s
  rw [← hf, ← Truncated.Edge.map_edge, ← Truncated.Edge.map_edge]
  have hArrow : Arrow.mk ((descNerve a).map (Truncated.HomotopyCategory.homMk f)) =
      Arrow.mk ((descNerve b).map (Truncated.HomotopyCategory.homMk f)) :=
    congr_arg (fun H ↦ H.mapArrow.obj (Arrow.mk (Truncated.HomotopyCategory.homMk f))) hab
  simp only [descNerve, descOfTruncation_map_homMk] at hArrow
  have he : ∀ (ψ : (truncation 2).obj Z ⟶ (truncation 2).obj (CategoryTheory.nerve D)),
      (f.map ψ).edge =
        CategoryTheory.ComposableArrows.mk₁ (CategoryTheory.nerve.homEquiv (f.map ψ)) :=
    fun ψ ↦ (CategoryTheory.ComposableArrows.mk₁_hom _).symm.trans
      (CategoryTheory.nerve.mk₁_homEquiv_apply (Edge.ofTruncated (f.map ψ))).symm
  rw [he, he]
  exact CategoryTheory.ComposableArrows.arrowEquiv.injective hArrow

/-! ## The nerve adjunction (equal universes)

`CategoryTheory.nerveAdjunction` and `Cat.{s, s}` force the object
and morphism universes of the target category to agree, so the
transpose, unit, and counit characterizations are isolated in this
section at a single universe `s`. -/

section

variable {Z : SSet.{s}} {D : Type s} [Category.{s} D]

/-- At a single universe, the universe-general truncated descent of
this module is the upstream small-category descent. -/
private theorem descOfTruncation_eq_upstream
    {V : SSet.Truncated.{s} 2} (φ : V ⟶ (truncation 2).obj (CategoryTheory.nerve D)) :
    descOfTruncation φ = Truncated.HomotopyCategory.descOfTruncation φ :=
  rfl

/-- The transpose of a map into a nerve across
`CategoryTheory.nerveAdjunction` is its descent to homotopy categories,
`SSet.descNerve`. -/
theorem nerveAdjunction_homEquiv_symm_apply (g : Z ⟶ CategoryTheory.nerve D) :
    (CategoryTheory.nerveAdjunction.homEquiv Z (Cat.of D)).symm g =
      (descNerve g).toCatHom := by
  have step1 : (CategoryTheory.nerveAdjunction.homEquiv Z (Cat.of D)).symm g =
      (((SSet.coskAdj 2).comp Truncated.nerve₂Adj).homEquiv Z (Cat.of D)).symm
        (g ≫ CategoryTheory.Nerve.cosk₂Iso.hom.app (Cat.of D)) :=
    Adjunction.homEquiv_ofNatIsoRight_symm_apply _ _ _
  rw [step1, Adjunction.comp_homEquiv]
  simp only [Equiv.symm_trans, Equiv.trans_apply]
  have step2 : ((SSet.coskAdj 2).homEquiv Z
        (CategoryTheory.Nerve.nerveFunctor₂.obj (Cat.of D))).symm
        (g ≫ CategoryTheory.Nerve.cosk₂Iso.hom.app (Cat.of D)) =
      (truncation 2).map g :=
    nerveTruncEquiv_apply g
  rw [step2]
  change (Truncated.nerve₂Adj.homEquiv ((truncation 2).obj Z) (Cat.of D)).symm
      ((truncation 2).map g) = (descNerve g).toCatHom
  rw [Truncated.nerve₂Adj, Adjunction.mkOfHomEquiv_homEquiv, descNerve,
    descOfTruncation_eq_upstream]
  rfl

/-- The descent of the canonical nerve-adjunction unit
`CategoryTheory.nerveAdjunction.unit.app Z` is the identity functor. This
is the adjunction unit-transpose identity read through
`SSet.nerveAdjunction_homEquiv_symm_apply`. -/
@[simp]
theorem descNerve_nerveAdjunction_unit_app (Z : SSet.{s}) :
    descNerve (CategoryTheory.nerveAdjunction.unit.app Z) =
      𝟭 Z.HomotopyCategory := by
  have h := nerveAdjunction_homEquiv_symm_apply
    (Z := Z) (D := Z.HomotopyCategory)
    (CategoryTheory.nerveAdjunction.unit.app Z)
  have hid : (CategoryTheory.nerveAdjunction.homEquiv Z
        (Cat.of Z.HomotopyCategory)).symm
        (CategoryTheory.nerveAdjunction.unit.app Z) =
      𝟙 (Cat.of Z.HomotopyCategory) :=
    Adjunction.homEquiv_symm_unit CategoryTheory.nerveAdjunction Z
  rw [hid] at h
  have hfun := congrArg Cat.Hom.toFunctor h
  simpa using hfun.symm

/-- The `2`-truncation of the canonical nerve-adjunction unit is the
truncated map classifying the identity functor. -/
@[simp]
theorem truncation_map_nerveAdjunction_unit_app (Z : SSet.{s}) :
    (truncation 2).map (CategoryTheory.nerveAdjunction.unit.app Z) =
      Truncated.HomotopyCategory.homToNerveMk
        (𝟭 ((truncation 2).obj Z).HomotopyCategory) := by
  apply Truncated.HomotopyCategory.functorEquiv.symm.injective
  change Truncated.HomotopyCategory.descOfTruncation
        ((truncation 2).map (CategoryTheory.nerveAdjunction.unit.app Z)) =
    Truncated.HomotopyCategory.descOfTruncation
      (Truncated.HomotopyCategory.homToNerveMk
        (𝟭 ((truncation 2).obj Z).HomotopyCategory))
  rw [← descOfTruncation_eq_upstream
    ((truncation 2).map (CategoryTheory.nerveAdjunction.unit.app Z))]
  change descNerve (CategoryTheory.nerveAdjunction.unit.app Z) = _
  rw [descNerve_nerveAdjunction_unit_app]
  exact (Truncated.HomotopyCategory.functorEquiv.left_inv _).symm

/-- The counit functor of `CategoryTheory.nerveAdjunction` at `D` is the
descent of the identity of `nerve D`; in particular its object and
generating-morphism formulas are those of `SSet.descNerve_obj_mk` and
`SSet.descNerve_map_homMk`. -/
theorem nerveAdjunction_counit_app_toFunctor :
    (CategoryTheory.nerveAdjunction.counit.app (Cat.of D)).toFunctor =
      descNerve (𝟙 (CategoryTheory.nerve D)) := by
  have h : CategoryTheory.nerveAdjunction.counit.app (Cat.of D) =
      (descNerve (𝟙 (CategoryTheory.nerve D))).toCatHom := by
    have hc := Adjunction.homEquiv_counit CategoryTheory.nerveAdjunction
      (CategoryTheory.nerve D) (Cat.of D) (𝟙 (CategoryTheory.nerve D))
    rw [nerveAdjunction_homEquiv_symm_apply] at hc
    have hid := congrArg
      (· ≫ CategoryTheory.nerveAdjunction.counit.app (Cat.of D))
      (hoFunctor.map_id (CategoryTheory.nerve D))
    exact (hid.trans (Category.id_comp _)).symm.trans hc.symm
  rw [h]
  rfl

end

/-! ## Evaluation at `Δ[0]` and edges at a vertex

Evaluation is the canonical `(SSet.evalDeltaZeroIso C).hom` from
`MathlibExt.AlgebraicTopology.SimplicialSet.Slice` (with evaluation at
the unit given by upstream `(MonoidalClosed.unitIsoSelf C).hom`);
its curry and vertex formulas `SSet.curry'_unitIsoSelf_hom`,
`SSet.curry'_evalDeltaZeroIso_hom`,
`SSet.evalDeltaZeroIso_hom_app_ihomVertexEquiv`,
`SSet.ihomVertexEquiv_eq`, `SSet.ihomVertexEquiv_ihom_map`, and
`SSet.yonedaEquiv_symm_ihomVertexEquiv` live in
`MathlibExt.AlgebraicTopology.SimplicialSet.IhomVertices` beside
`SSet.ihomVertexEquiv`. -/

/-- Mapping an edge along a composite of simplicial maps is mapping it
successively along the factors. -/
theorem Edge.map_map {X Y W : SSet.{s}} {x₀ x₁ : X _⦋0⦌} (e : Edge x₀ x₁)
    (f : X ⟶ Y) (g : Y ⟶ W) : (e.map f).map g = e.map (f ≫ g) :=
  Edge.ext rfl

variable {m₁ m₂ : Z ⟶ CategoryTheory.nerve D}

/-- The vertex of `nerve D` obtained by evaluating a map `m : Z ⟶ nerve D`
at a vertex `z` of `Z` through the internal-hom evaluation at `Δ[0]`:
precomposition with `const z` followed by `(SSet.evalDeltaZeroIso _).hom`
recovers `m.app _ z`. -/
theorem eval_app_pre_app_ihomVertexEquiv (m : Z ⟶ CategoryTheory.nerve D)
    (z : Z _⦋0⦌) :
    ((evalDeltaZeroIso (CategoryTheory.nerve D)).hom).app (op ⦋0⦌)
        (((MonoidalClosed.pre (const z)).app _).app (op ⦋0⦌)
          (ihomVertexEquiv Z _ m)) = m.app (op ⦋0⦌) z := by
  rw [ihomVertexEquiv_pre_app, evalDeltaZeroIso_hom_app_ihomVertexEquiv,
    show const z = yonedaEquiv.symm z from (yonedaEquiv_symm_zero z).symm,
    yonedaEquiv_comp, Equiv.apply_symm_apply]

/-- The edge in a nerve obtained by evaluating an edge `e` of the
simplicial functor object `Fun(Z, nerve D)` at a vertex `z` of `Z`:
precompose `e` with the constant map at `z` and evaluate at `Δ[0]`. Its
morphism in `D` under `CategoryTheory.nerve.homEquiv` is the
`z`-component of the natural transformation classified by `e`. -/
def edgeAtVertex (e : Edge (ihomVertexEquiv Z _ m₁) (ihomVertexEquiv Z _ m₂))
    (z : Z _⦋0⦌) :
    (CategoryTheory.nerve D).Edge (m₁.app (op ⦋0⦌) z) (m₂.app (op ⦋0⦌) z) :=
  ((e.map ((MonoidalClosed.pre (const z)).app _)).map
    ((evalDeltaZeroIso _).hom)).ofEq
    (eval_app_pre_app_ihomVertexEquiv m₁ z)
    (eval_app_pre_app_ihomVertexEquiv m₂ z)

theorem edgeAtVertex_edge (e : Edge (ihomVertexEquiv Z _ m₁)
    (ihomVertexEquiv Z _ m₂)) (z : Z _⦋0⦌) :
    (edgeAtVertex e z).edge =
      ((e.map ((MonoidalClosed.pre (const z)).app _)).map
        ((evalDeltaZeroIso _).hom)).edge :=
  rfl

@[simp]
theorem edgeAtVertex_edge_eq_app (e : Edge (ihomVertexEquiv Z _ m₁)
    (ihomVertexEquiv Z _ m₂)) (z : Z _⦋0⦌) :
    (edgeAtVertex e z).edge =
      ((evalDeltaZeroIso (CategoryTheory.nerve D)).hom).app (op ⦋1⦌)
        (((MonoidalClosed.pre (const z)).app _).app (op ⦋1⦌) e.edge) := by
  rw [edgeAtVertex_edge, Edge.map_edge, Edge.map_edge]

end SSet

end
