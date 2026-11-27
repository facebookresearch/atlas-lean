/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import Mathlib.AlgebraicTopology.Quasicategory.TwoTruncatedQuasicategory
public import MathlibExt.AlgebraicTopology.Quasicategory.EdgeEquivalence

/-!
# From equivalence edges to inverse structures in a quasicategory

This file is the converse companion to `EdgeEquivalence.lean`: for a
quasicategory `X`, an edge whose image under `SSet.HomotopyCategory.homMk`
is an isomorphism carries inverse data `SSet.Edge.InvStruct`.

`SSet.Truncated.HomotopyCategory` presents morphisms by paths of edges,
while `SSet.Truncated.HomotopyCategory₂` presents them by individual edges.
The comparison between the two presentations provides the single-edge
representatives and composition triangles needed for inverse data.

The original Formal-Math development is by Tsutomu Okano and Avocado.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory
open scoped SimplicialObject.Truncated
open scoped Simplicial

universe v u

namespace SSet.Truncated

variable {V : Truncated.{u} 2} [Quasicategory₂ V]

/-- The comparison functor from the path-quotient homotopy category
`SSet.Truncated.HomotopyCategory` to the edge-quotient category
`SSet.Truncated.HomotopyCategory₂` of a `2`-truncated quasicategory.
It is the identity on vertices and sends `homMk e` to the homotopy
class of the same edge. -/
noncomputable def HomotopyCategory.toHomotopyCategory₂ :
    V.HomotopyCategory ⥤ HomotopyCategory₂ V :=
  HomotopyCategory.lift (D := HomotopyCategory₂ V)
    (fun x ↦ HomotopyCategory₂.mk x)
    (fun e ↦ HomotopyCategory₂.homMk e)
    (fun x ↦ HomotopyCategory₂.homMk_id (HomotopyCategory₂.mk x))
    (fun h ↦ h.homotopyCategory₂_fac)

/-- The comparison functor is the identity on vertex objects. -/
@[simp]
lemma HomotopyCategory.toHomotopyCategory₂_obj_mk (x : V _⦋0⦌₂) :
    HomotopyCategory.toHomotopyCategory₂.obj (HomotopyCategory.mk x) =
      HomotopyCategory₂.mk x :=
  HomotopyCategory.lift_obj_mk _ _ _ _ x

/-- The comparison functor sends `homMk e` to the homotopy class of
the same edge in `HomotopyCategory₂`. -/
@[simp]
lemma HomotopyCategory.toHomotopyCategory₂_map_homMk
    {x y : V _⦋0⦌₂} (e : Edge x y) :
    HomotopyCategory.toHomotopyCategory₂.map (HomotopyCategory.homMk e) =
      HomotopyCategory₂.homMk e :=
  HomotopyCategory.lift_map_homMk _ _ _ _ e

/-- The comparison functor from the edge-quotient category
`SSet.Truncated.HomotopyCategory₂` back to the path-quotient
`SSet.Truncated.HomotopyCategory` of a `2`-truncated quasicategory.
It is the identity on vertices and sends the homotopy class of an
edge to its `homMk` image. -/
noncomputable def HomotopyCategory₂.toHomotopyCategory :
    HomotopyCategory₂ V ⥤ V.HomotopyCategory :=
  HomotopyCategory₂.desc
    (fun x ↦ HomotopyCategory.mk x)
    (fun e ↦ HomotopyCategory.homMk e)
    (fun x ↦ HomotopyCategory.homMk_id x)
    (fun h ↦ HomotopyCategory.homMk_comp_homMk h)

/-- The backwards comparison functor is the identity on vertex
objects. -/
@[simp]
lemma HomotopyCategory₂.toHomotopyCategory_obj_mk
    (x : V _⦋0⦌₂) :
    HomotopyCategory₂.toHomotopyCategory.obj (HomotopyCategory₂.mk x) =
      HomotopyCategory.mk x :=
  rfl

/-- The backwards comparison functor sends the homotopy class of an
edge to its `homMk` image in the path-quotient category. -/
@[simp]
lemma HomotopyCategory₂.toHomotopyCategory_map_homMk
    {x y : V _⦋0⦌₂} (e : Edge x y) :
    HomotopyCategory₂.toHomotopyCategory.map
        (HomotopyCategory₂.homMk e) =
      HomotopyCategory.homMk e :=
  HomotopyCategory₂.desc_map_homMk _ _ _ _ e

/-- The two comparison functors are mutually inverse on morphisms of
the path-quotient category: mapping a morphism to `HomotopyCategory₂`
and back recovers it. This is proved by `hom_rec` induction — the
generating case is the two `homMk` compatibilities, and the
composition case is functoriality. -/
lemma HomotopyCategory₂.toHomotopyCategory_map_toHomotopyCategory₂_map
    {x y : V.HomotopyCategory} (f : x ⟶ y) :
    HomotopyCategory₂.toHomotopyCategory.map
        (HomotopyCategory.toHomotopyCategory₂.map f) =
      f := by
  induction f using HomotopyCategory.hom_rec with
  | homMk e =>
    rw [HomotopyCategory.toHomotopyCategory₂_map_homMk]
    exact HomotopyCategory₂.toHomotopyCategory_map_homMk e
  | comp f g hf hg =>
    rw [Functor.map_comp, Functor.map_comp, hf, hg]
    rfl

/-- The two comparison functors are mutually inverse on morphisms of
`HomotopyCategory₂`: every such morphism is the class of an edge by
`HomotopyCategory₂.homMk_surjective`, and the round trip fixes edge
classes. -/
lemma HomotopyCategory.toHomotopyCategory₂_map_toHomotopyCategory_map
    {x y : HomotopyCategory₂ V} (g : x ⟶ y) :
    HomotopyCategory.toHomotopyCategory₂.map
        (HomotopyCategory₂.toHomotopyCategory.map g) =
      g := by
  obtain ⟨e, rfl⟩ := HomotopyCategory₂.homMk_surjective g
  rw [HomotopyCategory₂.toHomotopyCategory_map_homMk]
  exact HomotopyCategory.toHomotopyCategory₂_map_homMk e

/-- In a `2`-truncated quasicategory, every morphism between vertex
objects of the path-quotient homotopy category is represented by a
single edge: paths compress to edges. -/
lemma HomotopyCategory.exists_homMk_eq {a b : V _⦋0⦌₂}
    (f : HomotopyCategory.mk a ⟶ HomotopyCategory.mk b) :
    ∃ e : Edge a b, HomotopyCategory.homMk e = f := by
  obtain ⟨e, he⟩ := HomotopyCategory₂.homMk_surjective
    (HomotopyCategory.toHomotopyCategory₂.map f)
  refine ⟨e, ?_⟩
  rw [← HomotopyCategory₂.toHomotopyCategory_map_toHomotopyCategory₂_map f,
    ← he]
  exact (HomotopyCategory₂.toHomotopyCategory_map_homMk e).symm

/-- In a `2`-truncated quasicategory, a composition relation between
edge classes in the path-quotient homotopy category is witnessed by
a `2`-simplex: if `homMk e₁ ≫ homMk e₂ = homMk e₃` there, then
`Edge.CompStruct e₁ e₂ e₃` is nonempty. -/
lemma Edge.CompStruct.nonempty_of_homotopyCategory_homMk_comp_eq
    {a b c : V _⦋0⦌₂} {e₁ : Edge a b} {e₂ : Edge b c} {e₃ : Edge a c}
    (h : HomotopyCategory.homMk e₁ ≫ HomotopyCategory.homMk e₂ =
      HomotopyCategory.homMk e₃) :
    Nonempty (Edge.CompStruct e₁ e₂ e₃) := by
  refine Edge.CompStruct.nonempty_iff.mpr ?_
  have step1 := congr_arg HomotopyCategory.toHomotopyCategory₂.map h
  rw [HomotopyCategory.toHomotopyCategory₂.map_comp,
    HomotopyCategory.toHomotopyCategory₂_map_homMk,
    HomotopyCategory.toHomotopyCategory₂_map_homMk,
    HomotopyCategory.toHomotopyCategory₂_map_homMk] at step1
  exact step1

end SSet.Truncated

namespace SSet

namespace Edge

variable {X : SSet.{u}} {x₀ x₁ x₂ : X _⦋0⦌}

/-- Every morphism between vertex objects in `SSet.hoFunctor.obj X`,
for a quasicategory `X`, is represented by a single edge. This is
`SSet.Truncated.HomotopyCategory.exists_homMk_eq` read through the
native `HomotopyCategory.homMk`. -/
theorem exists_homMk_eq [Quasicategory X]
    (f : (HomotopyCategory.mk x₀ : hoFunctor.obj X) ⟶
      (HomotopyCategory.mk x₁ : hoFunctor.obj X)) :
    ∃ e : Edge x₀ x₁, (HomotopyCategory.homMk e) = f := by
  obtain ⟨e, he⟩ := Truncated.HomotopyCategory.exists_homMk_eq
    (V := (truncation 2).obj X) f
  exact ⟨Edge.ofTruncated e, he⟩

/-- A composition relation between edge classes in the homotopy
category of a quasicategory is witnessed by a `2`-simplex:
if `HomotopyCategory.homMk e₀₁ ≫ HomotopyCategory.homMk e₁₂ = HomotopyCategory.homMk e₀₂`, then
`Edge.CompStruct e₀₁ e₁₂ e₀₂` is nonempty. -/
theorem nonempty_compStruct_of_homMk_comp_eq [Quasicategory X]
    {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₀₂ : Edge x₀ x₂}
    (h : HomotopyCategory.homMk e₀₁ ≫ HomotopyCategory.homMk e₁₂ =
      HomotopyCategory.homMk e₀₂) :
    Nonempty (Edge.CompStruct e₀₁ e₁₂ e₀₂) := by
  obtain ⟨c⟩ :=
    Truncated.Edge.CompStruct.nonempty_of_homotopyCategory_homMk_comp_eq
      (V := (truncation 2).obj X) h
  exact ⟨Edge.CompStruct.ofTruncated c⟩

/-- Main converse (the supporting results): in a quasicategory, an equivalence
edge carries inverse data. The inverse morphism of `(HomotopyCategory.homMk e)` in
the homotopy category is represented by an edge
(`exists_homMk_eq`), and the two inverse relations are lifted to
`CompStruct` witnesses (`nonempty_compStruct_of_homMk_comp_eq`). -/
theorem IsEquivalence.nonempty_invStruct [Quasicategory X]
    {e : Edge x₀ x₁} (h : e.IsEquivalence) : Nonempty e.InvStruct := by
  have hIso : IsIso (HomotopyCategory.homMk e) := (isEquivalence_iff e).mp h
  obtain ⟨g, hg₁, hg₂⟩ := hIso.out
  obtain ⟨einv, heinv⟩ := exists_homMk_eq g
  have hcomp₁ : HomotopyCategory.homMk e ≫ HomotopyCategory.homMk einv =
      HomotopyCategory.homMk (Edge.id x₀) := by
    rw [heinv, HomotopyCategory.homMk_id]
    exact hg₁
  have hcomp₂ : HomotopyCategory.homMk einv ≫ HomotopyCategory.homMk e =
      HomotopyCategory.homMk (Edge.id x₁) := by
    rw [heinv, HomotopyCategory.homMk_id]
    exact hg₂
  obtain ⟨c₁⟩ := nonempty_compStruct_of_homMk_comp_eq hcomp₁
  obtain ⟨c₂⟩ := nonempty_compStruct_of_homMk_comp_eq hcomp₂
  exact ⟨{ inv := einv, homInvId := c₁, invHomId := c₂ }⟩

/-- In a quasicategory, an edge is an equivalence if and only if it
carries inverse data. The backwards direction is
`SSet.Edge.InvStruct.isEquivalence` and holds in any simplicial
set; the forwards direction is `IsEquivalence.nonempty_invStruct`
and uses the quasicategory hypothesis. -/
theorem isEquivalence_iff_nonempty_invStruct [Quasicategory X]
    {e : Edge x₀ x₁} :
    e.IsEquivalence ↔ Nonempty e.InvStruct :=
  ⟨fun h ↦ h.nonempty_invStruct, fun ⟨I⟩ ↦ I.isEquivalence⟩

section CoherentIsoForward

/-- If the map `Δ[1] ⟶ X` classified by an edge extends along the
map `Δ[1] ⟶ SSet.coherentIso` classified by `coherentIso.hom`, then
the edge carries inverse data (and hence is an equivalence, by
`SSet.Edge.InvStruct.isEquivalence`). This is the forward chain
extension `⇒ Nonempty InvStruct ⇒ IsEquivalence`, for an
arbitrary simplicial set with no quasicategory hypothesis. -/
theorem nonempty_invStruct_of_coherentIso_extension
    {e : Edge x₀ x₁}
    (hex : ∃ g : coherentIso.{u} ⟶ X,
      yonedaEquiv.symm coherentIso.hom.edge ≫ g =
        yonedaEquiv.symm e.edge) :
    Nonempty e.InvStruct := by
  obtain ⟨g, hg⟩ := hex
  refine ⟨coherentIso.invStructOfEqMapHom (g := g) ?_⟩
  have h := congr_arg yonedaEquiv hg
  rw [yonedaEquiv_comp] at h
  simpa using h.symm

end CoherentIsoForward

section NerveExtension

variable {C : Type u} [Category.{v} C]

/-- The map `SSet.coherentIso ⟶ nerve C` classified by an isomorphism
of `C`, given by postcomposing composable strings with
`WalkingIso.fromIso`. This inlines the app formula of
`CategoryTheory.nerveMap`, whose stated signature forces the two
categories to share a morphism universe, which `WalkingIso` (a
codiscrete category, with `Unit` morphisms in universe `0`) and a
general `C` do not. -/
private def nerveMapOfIso {a b : C} (i : a ≅ b) :
    coherentIso.{max u v} ⟶ CategoryTheory.nerve C :=
  { app _ := ↾fun X ↦
      ((CategoryTheory.WalkingIso.fromIso.{max u v, u, v} i).mapComposableArrows
        _).obj X }

set_option linter.flexible false in
/-- The map classified by an isomorphism sends the forward edge of
`SSet.coherentIso` to the `1`-simplex of the isomorphism. -/
private lemma nerveMapOfIso_app_hom_edge {a b : C} (i : a ≅ b) :
    (nerveMapOfIso i).app _ coherentIso.hom.edge =
      ComposableArrows.mk₁ i.hom := by
  change ((CategoryTheory.WalkingIso.fromIso.{max u v, u, v} i).mapComposableArrows
      1).obj (ComposableArrows.mk₁ CategoryTheory.WalkingIso.iso.hom) = _
  exact ComposableArrows.ext₁ rfl rfl
    (by simp; exact (Category.id_comp _).symm)

/-- The `1`-simplex `ComposableArrows.mk₁ (nerve.homEquiv e)` of a
nerve edge is the edge itself, by the left-inverse law of
`CategoryTheory.nerve.homEquiv`. -/
private lemma nerveMk₁HomEquivEqEdge
    {x y : (CategoryTheory.nerve C) _⦋0⦌}
    (e : (CategoryTheory.nerve C).Edge x y) :
    ComposableArrows.mk₁ (CategoryTheory.nerve.homEquiv e) = e.edge := by
  have h := congr_arg Edge.edge (CategoryTheory.nerve.homEquiv.left_inv e)
  exact h

/-- Nerve gate for extensions: an equivalence edge in the nerve of
a category extends along the endpoint inclusion
`Δ[1] ⟶ SSet.coherentIso`. The extending map is the nerve map
classified by the isomorphism `nerve.homEquiv e`, which exists by
`SSet.Edge.isEquivalence_nerve_iff`. This proves the full
extension characterization for nerves, the one case where a
`coherentIso` extension is formal from inverse data because both
source and target are nerves. -/
theorem IsEquivalence.exists_coherentIso_extension_nerve
    {x y : (CategoryTheory.nerve C) _⦋0⦌}
    {e : (CategoryTheory.nerve C).Edge x y} (h : e.IsEquivalence) :
    ∃ g : coherentIso.{max u v} ⟶ CategoryTheory.nerve C,
      yonedaEquiv.symm coherentIso.hom.edge ≫ g =
        yonedaEquiv.symm e.edge := by
  have hIso : IsIso (CategoryTheory.nerve.homEquiv e) :=
    (isEquivalence_nerve_iff e).mp h
  obtain ⟨ginv, h₁, h₂⟩ := hIso.out
  let i : CategoryTheory.nerveEquiv x ≅ CategoryTheory.nerveEquiv y :=
    { hom := CategoryTheory.nerve.homEquiv e, inv := ginv,
      hom_inv_id := h₁, inv_hom_id := h₂ }
  refine ⟨nerveMapOfIso i, ?_⟩
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp]
  simp only [Equiv.apply_symm_apply]
  rw [nerveMapOfIso_app_hom_edge]
  exact nerveMk₁HomEquivEqEdge e

/-- For an edge in the nerve of a category, being an equivalence is
equivalent to extending along the endpoint inclusion
`Δ[1] ⟶ SSet.coherentIso`. The backwards direction is
`SSet.Edge.isEquivalence_of_coherentIso_extension` and holds for an
arbitrary simplicial set. -/
theorem isEquivalence_nerve_iff_coherentIso_extension
    {x y : (CategoryTheory.nerve C) _⦋0⦌}
    (e : (CategoryTheory.nerve C).Edge x y) :
    e.IsEquivalence ↔
      ∃ g : coherentIso.{max u v} ⟶ CategoryTheory.nerve C,
        yonedaEquiv.symm coherentIso.hom.edge ≫ g =
          yonedaEquiv.symm e.edge :=
  ⟨fun h ↦ h.exists_coherentIso_extension_nerve,
    fun h ↦ isEquivalence_of_coherentIso_extension h⟩

end NerveExtension

end Edge

end SSet
