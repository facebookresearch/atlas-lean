/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.Quasicategory.EdgeEquivalence

/-!
# Tests for equivalence edges in a simplicial set

Public clients exercise `SSet.Edge.IsEquivalence` on Mathlib's
`SSet.HomotopyCategory.homMk`, together with identity, composition,
map-preservation, inverse structures, coherent-isomorphism extensions,
and both directions of the nerve criterion.

The original Formal-Math development is by Tsutomu Okano and Avocado.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory
open scoped Simplicial

universe v u

namespace MathlibExtTest.AlgebraicTopology.Quasicategory
namespace EdgeEquivalenceTest

open SSet

section Basic

variable {X Y : SSet.{u}} {x₀ x₁ x₂ : X _⦋0⦌}

/-- The equivalence predicate tests the native homotopy-category morphism. -/
example (e : Edge x₀ x₁) : e.IsEquivalence ↔ IsIso (HomotopyCategory.homMk e) :=
  Edge.isEquivalence_iff e

/-- The identity edge is an equivalence. -/
example (x : X _⦋0⦌) : (Edge.id x).IsEquivalence :=
  Edge.isEquivalence_id x

/-- Equivalences are preserved by simplicial maps. -/
example {e : Edge x₀ x₁} (h : e.IsEquivalence) (f : X ⟶ Y) :
    (e.map f).IsEquivalence :=
  h.map f

/-- Identity equivalences are preserved by simplicial maps. -/
example (x : X _⦋0⦌) (f : X ⟶ Y) :
    ((Edge.id x).map f).IsEquivalence :=
  (Edge.isEquivalence_id x).map f

/-- Inverse data gives an isomorphism in the homotopy category. -/
example {e : Edge x₀ x₁} (I : e.InvStruct) :
    I.toHoIso.hom = HomotopyCategory.homMk e ∧
      I.toHoIso.inv = HomotopyCategory.homMk I.inv :=
  ⟨Edge.InvStruct.toHoIso_hom I, Edge.InvStruct.toHoIso_inv I⟩

/-- Inverse data makes an edge an equivalence. -/
example {e : Edge x₀ x₁} (I : e.InvStruct) : e.IsEquivalence :=
  I.isEquivalence

/-- Composites of equivalences, along a `CompStruct`, are
equivalences. -/
example {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₀₂ : Edge x₀ x₂}
    (h : Edge.CompStruct e₀₁ e₁₂ e₀₂) (h₀₁ : e₀₁.IsEquivalence)
    (h₁₂ : e₁₂.IsEquivalence) : e₀₂.IsEquivalence :=
  Edge.IsEquivalence.of_compStruct h h₀₁ h₁₂

/-- Composition with identity edges keeps an equivalence. -/
example {e : Edge x₀ x₁} (h : e.IsEquivalence) : e.IsEquivalence :=
  Edge.IsEquivalence.of_compStruct (Edge.CompStruct.idComp e)
    (Edge.isEquivalence_id x₀) h

end Basic

section CoherentIsoTests

variable {X : SSet.{u}} {x₀ x₁ : X _⦋0⦌}

/-- The forward edge of the coherent isomorphism is an equivalence. -/
example : coherentIso.hom.IsEquivalence :=
  Edge.isEquivalence_coherentIso_hom

/-- The backwards edge is the inverse edge of the forward edge, and is
itself an equivalence through the flipped inverse structure. -/
example : coherentIso.inv.IsEquivalence :=
  coherentIso.invStructHom.invStructInv.isEquivalence

/-- An edge that is the image of `coherentIso.hom` under a map out of
`coherentIso` is an equivalence; here the identity map. -/
example : (coherentIso.hom.{u}).IsEquivalence :=
  Edge.isEquivalence_of_eq_map_coherentIso_hom (g := 𝟙 coherentIso.{u})
    (by simp)

/-- Extension form with the identity map of `coherentIso`. -/
example : (coherentIso.hom.{u}).IsEquivalence :=
  Edge.isEquivalence_of_coherentIso_extension
    ⟨𝟙 coherentIso.{u}, by simp⟩

/-- Extension form for a general edge and an extending map. -/
example {e : Edge x₀ x₁} (g : coherentIso.{u} ⟶ X)
    (h : e.edge = g.app _ coherentIso.hom.edge) : e.IsEquivalence :=
  Edge.isEquivalence_of_eq_map_coherentIso_hom h

/-- The image of `coherentIso.hom` under any map is an equivalence. -/
example (g : coherentIso.{u} ⟶ X) :
    (coherentIso.hom.map g).IsEquivalence :=
  Edge.isEquivalence_coherentIso_hom.map g

end CoherentIsoTests

section NerveTests

variable {C : Type u} [Category.{v} C]

/-- Nerve gate as an if-and-only-if through `nerve.homEquiv`. -/
example {x y : (nerve C) _⦋0⦌} (e : (nerve C).Edge x y) :
    e.IsEquivalence ↔ IsIso (nerve.homEquiv e) :=
  Edge.isEquivalence_nerve_iff e

/-- Forward direction of the nerve gate. -/
example {x y : (nerve C) _⦋0⦌} (e : (nerve C).Edge x y)
    (h : e.IsEquivalence) : IsIso (nerve.homEquiv e) :=
  (Edge.isEquivalence_nerve_iff e).mp h

/-- Reverse direction of the nerve gate. -/
example {x y : (nerve C) _⦋0⦌} (e : (nerve C).Edge x y)
    (h : IsIso (nerve.homEquiv e)) : e.IsEquivalence :=
  (Edge.isEquivalence_nerve_iff e).mpr h

/-- Nerve gate for the identity edge of a nerve, forward direction. -/
example (x : (nerve C) _⦋0⦌) :
    IsIso (nerve.homEquiv (Edge.id x)) :=
  (Edge.isEquivalence_nerve_iff _).mp (Edge.isEquivalence_id x)

/-- Nerve gate in `nerve.edgeMk` form. -/
example {a b : C} (f : a ⟶ b) :
    (nerve.edgeMk f).IsEquivalence ↔ IsIso f :=
  Edge.isEquivalence_nerve_edgeMk_iff f

/-- The edge of an isomorphism in `C` is an equivalence in the nerve. -/
example {a b : C} (f : a ⟶ b) [IsIso f] :
    (nerve.edgeMk f).IsEquivalence :=
  (Edge.isEquivalence_nerve_edgeMk_iff f).mpr inferInstance

/-- An equivalence edge of the form `nerve.edgeMk f` comes from an
isomorphism in `C`. -/
example {a b : C} (f : a ⟶ b)
    (h : (nerve.edgeMk f).IsEquivalence) : IsIso f :=
  (Edge.isEquivalence_nerve_edgeMk_iff f).mp h

/-- The identity morphism of `C` gives an equivalence edge. -/
example (a : C) : (nerve.edgeMk (𝟙 a)).IsEquivalence :=
  (Edge.isEquivalence_nerve_edgeMk_iff (𝟙 a)).mpr inferInstance

/-- The noninvertible inequality `0 ≤ 1` in `Fin 2` gives a
non-equivalence edge in its nerve. -/
example : ¬ (nerve.edgeMk
    (homOfLE (show (0 : Fin 2) ≤ 1 by decide))).IsEquivalence := by
  rw [Edge.isEquivalence_nerve_edgeMk_iff]
  intro h
  obtain ⟨backward, _, _⟩ := h.out
  exact (by decide : ¬ ((1 : Fin 2) ≤ 0)) (leOfHom backward)

/-- Nerve gate at the same-universe specialization used by
`SSet.nerveAdjunction`. -/
example {D : Type u} [Category.{u} D] {a b : D} (f : a ⟶ b) :
    (nerve.edgeMk f).IsEquivalence ↔ IsIso f :=
  Edge.isEquivalence_nerve_edgeMk_iff f

end NerveTests

end EdgeEquivalenceTest
end MathlibExtTest.AlgebraicTopology.Quasicategory
