/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.SimplicialSet.CoherentIso
public import Mathlib.AlgebraicTopology.SimplicialSet.HomotopyCat
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex

/-!
# Equivalence edges in a simplicial set

For a simplicial set `X`, an edge is an *equivalence* when the morphism it
represents in the homotopy category `SSet.hoFunctor.obj X` is an
isomorphism. This file introduces that predicate on top of the upstream
`SSet.Edge` / `Edge.CompStruct` / `Edge.InvStruct` API and the quotient
presentation `SSet.HomotopyCategory.homMk`:
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory
open scoped SimplicialObject.Truncated
open scoped Simplicial

universe v u

namespace SSet

namespace Edge

variable {X Y : SSet.{u}} {x₀ x₁ x₂ : X _⦋0⦌}

/-- The morphism in the homotopy category `SSet.hoFunctor.obj X`
represented by an edge. This is `SSet.HomotopyCategory.homMk`, typed in
the `Cat`-valued `SSet.hoFunctor`. -/
def toHoHom (e : Edge x₀ x₁) :
    (HomotopyCategory.mk x₀ : hoFunctor.obj X) ⟶
      (HomotopyCategory.mk x₁ : hoFunctor.obj X) :=
  HomotopyCategory.homMk e

/-- `Edge.toHoHom` is definitionally `SSet.HomotopyCategory.homMk`. -/
@[simp]
lemma toHoHom_eq_homMk (e : Edge x₀ x₁) :
    e.toHoHom = HomotopyCategory.homMk e :=
  rfl

/-- The identity edge represents the identity morphism of the homotopy
category. -/
lemma toHoHom_id (x : X _⦋0⦌) :
    (Edge.id x).toHoHom =
      𝟙 (HomotopyCategory.mk x : hoFunctor.obj X) :=
  HomotopyCategory.homMk_id x

/-- A `CompStruct` witnesses composition of the represented morphisms
in the homotopy category. -/
@[reassoc]
lemma toHoHom_comp {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂}
    {e₀₂ : Edge x₀ x₂} (h : Edge.CompStruct e₀₁ e₁₂ e₀₂) :
    e₀₁.toHoHom ≫ e₁₂.toHoHom = e₀₂.toHoHom :=
  HomotopyCategory.homMk_comp_homMk h

/-- The morphism represented by a transported edge is the image of the
represented morphism under `SSet.mapHomotopyCategory`, the functor
underlying `SSet.hoFunctor.map`. -/
lemma toHoHom_map (e : Edge x₀ x₁) (f : X ⟶ Y) :
    (e.map f).toHoHom = (mapHomotopyCategory f).map e.toHoHom :=
  rfl

/-- An edge is an *equivalence* when the morphism it represents in the
homotopy category `SSet.hoFunctor.obj X` is an isomorphism. -/
def IsEquivalence (e : Edge x₀ x₁) : Prop :=
  IsIso e.toHoHom

/-- An edge is an equivalence if and only if its image in the homotopy
category is an isomorphism. -/
lemma isEquivalence_iff (e : Edge x₀ x₁) :
    e.IsEquivalence ↔ IsIso e.toHoHom :=
  Iff.rfl

/-- The identity edge represents an isomorphism of the homotopy
category. -/
instance (x : X _⦋0⦌) : IsIso (Edge.id x).toHoHom := by
  rw [toHoHom_id]
  infer_instance

/-- The identity edge is an equivalence. -/
theorem isEquivalence_id (x : X _⦋0⦌) : (Edge.id x).IsEquivalence :=
  inferInstanceAs (IsIso (Edge.id x).toHoHom)

/-- Equivalences are preserved by maps of simplicial sets: the image of
an equivalence edge under `f : X ⟶ Y` is an equivalence edge of `Y`. -/
theorem IsEquivalence.map {e : Edge x₀ x₁} (h : e.IsEquivalence)
    (f : X ⟶ Y) : (e.map f).IsEquivalence := by
  rw [isEquivalence_iff, toHoHom_map]
  exact @Functor.map_isIso _ _ _ _ _ _ _ _
    ((isEquivalence_iff e).mp h)

/-- The isomorphism in the homotopy category determined by inverse
data `e.InvStruct`. -/
def InvStruct.toHoIso {e : Edge x₀ x₁} (I : e.InvStruct) :
    (HomotopyCategory.mk x₀ : hoFunctor.obj X) ≅
      (HomotopyCategory.mk x₁ : hoFunctor.obj X) where
  hom := e.toHoHom
  inv := I.inv.toHoHom
  hom_inv_id := by rw [toHoHom_comp I.homInvId, toHoHom_id]
  inv_hom_id := by rw [toHoHom_comp I.invHomId, toHoHom_id]

/-- The forward morphism of `InvStruct.toHoIso` is the morphism
represented by the edge. -/
@[simp]
lemma InvStruct.toHoIso_hom {e : Edge x₀ x₁} (I : e.InvStruct) :
    I.toHoIso.hom = e.toHoHom :=
  rfl

/-- The backward morphism of `InvStruct.toHoIso` is the morphism
represented by the inverse edge. -/
@[simp]
lemma InvStruct.toHoIso_inv {e : Edge x₀ x₁} (I : e.InvStruct) :
    I.toHoIso.inv = I.inv.toHoHom :=
  rfl

/-- Inverse data makes an edge an equivalence: the represented
morphism is an isomorphism with inverse represented by the backward
edge. -/
theorem InvStruct.isEquivalence {e : Edge x₀ x₁} (I : e.InvStruct) :
    e.IsEquivalence :=
  ⟨⟨I.inv.toHoHom, by rw [toHoHom_comp I.homInvId, toHoHom_id],
    by rw [toHoHom_comp I.invHomId, toHoHom_id]⟩⟩

/-- Inverse data makes an edge an equivalence. -/
theorem isEquivalence_of_invStruct {e : Edge x₀ x₁}
    (I : e.InvStruct) : e.IsEquivalence :=
  I.isEquivalence

/-- If two composable edges are equivalences and are composed according
to a `CompStruct`, then their composite edge is an equivalence. -/
theorem IsEquivalence.of_compStruct {e₀₁ : Edge x₀ x₁}
    {e₁₂ : Edge x₁ x₂} {e₀₂ : Edge x₀ x₂}
    (h : Edge.CompStruct e₀₁ e₁₂ e₀₂) (h₀₁ : e₀₁.IsEquivalence)
    (h₁₂ : e₁₂.IsEquivalence) : e₀₂.IsEquivalence := by
  rw [isEquivalence_iff, ← toHoHom_comp h]
  exact IsIso.comp_isIso' ((isEquivalence_iff _).mp h₀₁)
    ((isEquivalence_iff _).mp h₁₂)

section CoherentIso

/-- The forward edge of `SSet.coherentIso` is an equivalence. -/
theorem isEquivalence_coherentIso_hom :
    coherentIso.hom.IsEquivalence :=
  coherentIso.invStructHom.isEquivalence

/-- If an edge is the image of the forward edge of `SSet.coherentIso`
under a map `g : SSet.coherentIso ⟶ X`, then it is an equivalence.
This is `SSet.coherentIso.invStructOfEqMapHom` read through
`InvStruct.isEquivalence`. -/
theorem isEquivalence_of_eq_map_coherentIso_hom {e : Edge x₀ x₁}
    {g : coherentIso.{u} ⟶ X}
    (h : e.edge = g.app _ coherentIso.hom.edge) : e.IsEquivalence :=
  (coherentIso.invStructOfEqMapHom h).isEquivalence

/-- If the map `Δ[1] ⟶ X` classified by an edge extends along the map
`Δ[1] ⟶ SSet.coherentIso` classified by `coherentIso.hom`, then the
edge is an equivalence. -/
theorem isEquivalence_of_coherentIso_extension {e : Edge x₀ x₁}
    (hex : ∃ g : coherentIso.{u} ⟶ X,
      yonedaEquiv.symm coherentIso.hom.edge ≫ g =
        yonedaEquiv.symm e.edge) : e.IsEquivalence := by
  obtain ⟨g, hg⟩ := hex
  refine isEquivalence_of_eq_map_coherentIso_hom (g := g) ?_
  have h := congr_arg yonedaEquiv hg
  rw [yonedaEquiv_comp] at h
  simpa using h.symm

end CoherentIso

section Nerve

variable {C : Type u} [Category.{v} C]

/-- Compatibility of `nerve.homEquiv` with composition, stated for
`2`-truncated edges of a nerve so that it can feed
`Truncated.HomotopyCategory.lift`. -/
private lemma nerveHomEquivCompOfTruncated
    {x₀ x₁ x₂ : ((truncation 2).obj (nerve C)) _⦋0⦌₂}
    {e₀₁ : Truncated.Edge x₀ x₁} {e₁₂ : Truncated.Edge x₁ x₂}
    {e₀₂ : Truncated.Edge x₀ x₂}
    (h : Truncated.Edge.CompStruct e₀₁ e₁₂ e₀₂) :
    nerve.homEquiv (Edge.ofTruncated e₀₁) ≫
        nerve.homEquiv (Edge.ofTruncated e₁₂) =
      nerve.homEquiv (Edge.ofTruncated e₀₂) :=
  nerve.homEquiv_comp (Edge.CompStruct.ofTruncated h)

/-- The functor from the homotopy category of a nerve to the original
category, obtained from the universal property
`Truncated.HomotopyCategory.lift` using `nerve.homEquiv`. This is a
`2`-truncated lift analogous to the counit functor of
`SSet.nerveAdjunction`; no equality with that counit functor is
asserted here. -/
private noncomputable def nerveHoFunctorToCat :
    (nerve C).HomotopyCategory ⥤ C :=
  Truncated.HomotopyCategory.lift (V := (truncation 2).obj (nerve C))
    (fun x ↦ nerveEquiv x)
    (fun e ↦ nerve.homEquiv (Edge.ofTruncated e))
    (fun x ↦ nerve.homEquiv_id x)
    (fun h ↦ nerveHomEquivCompOfTruncated h)

/-- The functor `nerveHoFunctorToCat` sends the morphism represented
by an edge of the nerve to the corresponding morphism of `C`. -/
private lemma nerveHoFunctorToCat_map_toHoHom
    {x y : (nerve C) _⦋0⦌} (e : (nerve C).Edge x y) :
    nerveHoFunctorToCat.map e.toHoHom = nerve.homEquiv e := by
  have h := Truncated.HomotopyCategory.lift_map_homMk
    (fun x ↦ nerveEquiv x)
    (fun e ↦ nerve.homEquiv (Edge.ofTruncated e))
    (fun x ↦ nerve.homEquiv_id x)
    (fun h ↦ nerveHomEquivCompOfTruncated h)
    e.toTruncated
  exact h

/-- Composition of the edges `nerve.homEquiv.symm f` and
`nerve.homEquiv.symm g` in a nerve is witnessed by the
`2`-simplex `ComposableArrows.mk₂ f g`. -/
private def nerveCompStructHomEquivSymm {x y z : (nerve C) _⦋0⦌}
    (f : nerveEquiv x ⟶ nerveEquiv y)
    (g : nerveEquiv y ⟶ nerveEquiv z) :
    CompStruct (nerve.homEquiv.symm f) (nerve.homEquiv.symm g)
      (nerve.homEquiv.symm (f ≫ g)) :=
  Edge.CompStruct.mk (ComposableArrows.mk₂ f g)
    (nerve.δ₂_mk₂_eq f g) (nerve.δ₀_mk₂_eq f g)
    (nerve.δ₁_mk₂_eq f g)

/-- The `1`-simplex `ComposableArrows.mk₁ (𝟙 _)` is the degenerate
simplex underlying an identity edge of a nerve. -/
private lemma nerveMk₁IdEqIdEdge (x : (nerve C) _⦋0⦌) :
    ComposableArrows.mk₁ (𝟙 (nerveEquiv x)) = (Edge.id x).edge := by
  rw [Edge.id_edge]
  conv_rhs => rw [← nerveEquiv.left_inv x]
  exact (nerve.σ_zero_nerveEquiv_symm _).symm

/-- If `f` is an isomorphism in `C`, the corresponding edge
`nerve.homEquiv.symm f` of the nerve has inverse data given by the
edge of `inv f`. -/
private noncomputable def nerveInvStructHomEquivSymmOfIsIso
    {x y : (nerve C) _⦋0⦌} (f : nerveEquiv x ⟶ nerveEquiv y)
    [IsIso f] : (nerve.homEquiv.symm f).InvStruct where
  inv := nerve.homEquiv.symm (inv f)
  homInvId := (nerveCompStructHomEquivSymm f (inv f)).ofEq rfl rfl
    (by rw [IsIso.hom_inv_id]; exact nerveMk₁IdEqIdEdge x)
  invHomId := (nerveCompStructHomEquivSymm (inv f) f).ofEq rfl rfl
    (by rw [IsIso.inv_hom_id]; exact nerveMk₁IdEqIdEdge y)

/-- Nerve gate: an edge in the nerve of a category is an equivalence
if and only if the corresponding morphism of the category, obtained
via `nerve.homEquiv`, is an isomorphism. Both directions are proved:
the forward direction maps along `nerveHoFunctorToCat`, and the
reverse direction uses the inverse morphism to build an
`Edge.InvStruct`. -/
theorem isEquivalence_nerve_iff {x y : (nerve C) _⦋0⦌}
    (e : (nerve C).Edge x y) :
    e.IsEquivalence ↔ IsIso (nerve.homEquiv e) := by
  constructor
  · intro h
    rw [← nerveHoFunctorToCat_map_toHoHom e]
    exact @Functor.map_isIso _ _ _ _ _ _ _ _
      ((isEquivalence_iff e).mp h)
  · intro h
    have h' : (nerve.homEquiv.symm (nerve.homEquiv e)).IsEquivalence :=
      (nerveInvStructHomEquivSymmOfIsIso
        (nerve.homEquiv e)).isEquivalence
    rwa [Equiv.symm_apply_apply] at h'

/-- Nerve gate, `nerve.edgeMk` form: for a morphism `f` of `C`, the
edge `nerve.edgeMk f` of the nerve is an equivalence if and only if
`f` is an isomorphism. -/
theorem isEquivalence_nerve_edgeMk_iff {a b : C} (f : a ⟶ b) :
    (nerve.edgeMk f).IsEquivalence ↔ IsIso f :=
  (isEquivalence_nerve_iff (nerve.edgeMk f)).trans (by
    rw [nerve.homEquiv_edgeMk]
    exact Iff.rfl)

end Nerve

end Edge

end SSet
