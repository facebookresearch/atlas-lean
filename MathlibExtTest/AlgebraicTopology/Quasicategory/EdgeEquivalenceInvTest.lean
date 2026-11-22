/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.Quasicategory.EdgeEquivalenceInv

/-!
# Tests for equivalence edges to inverse structures

Public clients exercise the `2`-truncated comparison functors and
their morphism-level inverse laws, edge representability and
`CompStruct` lifting in the path-quotient homotopy category, the
quasicategory characterization
`SSet.Edge.isEquivalence_iff_nonempty_invStruct`, the forward
coherent-isomorphism extension chain for arbitrary simplicial sets,
and the full extension if-and-only-if for nerves. Only public
declarations are used.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory
open scoped SimplicialObject.Truncated
open scoped Simplicial

universe v u

namespace MathlibExtTest.AlgebraicTopology.Quasicategory
namespace EdgeEquivalenceInvTest

open SSet

section Signatures


end Signatures

section TruncatedComparison

variable {V : Truncated.{u} 2} [Truncated.Quasicategory₂ V]
  {a b c : V _⦋0⦌₂}

/-- The forwards comparison functor fixes vertex objects. -/
example (x : V _⦋0⦌₂) :
    Truncated.HomotopyCategory.toHomotopyCategory₂.obj
        (Truncated.HomotopyCategory.mk x) =
      Truncated.HomotopyCategory₂.mk x :=
  Truncated.HomotopyCategory.toHomotopyCategory₂_obj_mk x

/-- The backwards comparison functor fixes vertex objects. -/
example (x : V _⦋0,Truncated.zero_le_two⦌₂) :
    Truncated.HomotopyCategory₂.toHomotopyCategory.obj
        (Truncated.HomotopyCategory₂.mk x) =
      Truncated.HomotopyCategory.mk x :=
  Truncated.HomotopyCategory₂.toHomotopyCategory_obj_mk x

/-- The forwards comparison functor sends `homMk` to the edge class
in `HomotopyCategory₂`. -/
example (e : Truncated.Edge a b) :
    Truncated.HomotopyCategory.toHomotopyCategory₂.map
        (Truncated.HomotopyCategory.homMk e) =
      Truncated.HomotopyCategory₂.homMk e :=
  Truncated.HomotopyCategory.toHomotopyCategory₂_map_homMk e

/-- The backwards comparison functor sends an edge class to `homMk`
in the path-quotient category. -/
example {a' b' : V _⦋0,Truncated.zero_le_two⦌₂}
    (e : Truncated.Edge a' b') :
    Truncated.HomotopyCategory₂.toHomotopyCategory.map
        (Truncated.HomotopyCategory₂.homMk e) =
      Truncated.HomotopyCategory.homMk e :=
  Truncated.HomotopyCategory₂.toHomotopyCategory_map_homMk e

/-- Round trip on a morphism of the path-quotient category is the
identity. -/
example {x y : V.HomotopyCategory} (f : x ⟶ y) :
    Truncated.HomotopyCategory₂.toHomotopyCategory.map
        (Truncated.HomotopyCategory.toHomotopyCategory₂.map f) =
      f :=
  Truncated.HomotopyCategory₂.toHomotopyCategory_map_toHomotopyCategory₂_map
    f

/-- Round trip on a morphism of `HomotopyCategory₂` is the
identity. -/
example {x y : Truncated.HomotopyCategory₂ V} (g : x ⟶ y) :
    Truncated.HomotopyCategory.toHomotopyCategory₂.map
        (Truncated.HomotopyCategory₂.toHomotopyCategory.map g) =
      g :=
  Truncated.HomotopyCategory.toHomotopyCategory₂_map_toHomotopyCategory_map
    g

/-- Round trip on a composite of edge classes is the identity. -/
example (e₁ : Truncated.Edge a b) (e₂ : Truncated.Edge b c) :
    Truncated.HomotopyCategory₂.toHomotopyCategory.map
        (Truncated.HomotopyCategory.toHomotopyCategory₂.map
          (Truncated.HomotopyCategory.homMk e₁ ≫
            Truncated.HomotopyCategory.homMk e₂)) =
      Truncated.HomotopyCategory.homMk e₁ ≫
        Truncated.HomotopyCategory.homMk e₂ :=
  Truncated.HomotopyCategory₂.toHomotopyCategory_map_toHomotopyCategory₂_map
    _

/-- A composite of two edge classes is represented by a single edge
(path compression). -/
example (e₁ : Truncated.Edge a b) (e₂ : Truncated.Edge b c) :
    ∃ e : Truncated.Edge a c,
      Truncated.HomotopyCategory.homMk e =
        Truncated.HomotopyCategory.homMk e₁ ≫
          Truncated.HomotopyCategory.homMk e₂ :=
  Truncated.HomotopyCategory.exists_homMk_eq _

/-- A length-three path is represented by a single edge. -/
example {d : V _⦋0⦌₂} (e₁ : Truncated.Edge a b)
    (e₂ : Truncated.Edge b c) (e₃ : Truncated.Edge c d) :
    ∃ e : Truncated.Edge a d,
      Truncated.HomotopyCategory.homMk e =
        Truncated.HomotopyCategory.homMk e₁ ≫
          Truncated.HomotopyCategory.homMk e₂ ≫
            Truncated.HomotopyCategory.homMk e₃ :=
  Truncated.HomotopyCategory.exists_homMk_eq _

/-- A composition relation in the path-quotient category lifts to a
`CompStruct`; here applied to the relation that a given `CompStruct`
itself induces. -/
example {e₁ : Truncated.Edge a b} {e₂ : Truncated.Edge b c}
    {e₃ : Truncated.Edge a c}
    (s : Truncated.Edge.CompStruct e₁ e₂ e₃) :
    Nonempty (Truncated.Edge.CompStruct e₁ e₂ e₃) :=
  Truncated.Edge.CompStruct.nonempty_of_homotopyCategory_homMk_comp_eq
    (Truncated.HomotopyCategory.homMk_comp_homMk s)

end TruncatedComparison

section QuasicategoryInvStruct

variable {X : SSet.{u}} [Quasicategory X] {x₀ x₁ x₂ : X _⦋0⦌}

/-- A composite of two edge classes in `hoFunctor.obj X` is
represented by a single edge. -/
example (e₁ : Edge x₀ x₁) (e₂ : Edge x₁ x₂) :
    ∃ e : Edge x₀ x₂, e.toHoHom = e₁.toHoHom ≫ e₂.toHoHom :=
  Edge.exists_toHoHom_eq _

/-- The identity morphism of a vertex object is represented by an
edge. -/
example (x : X _⦋0⦌) :
    ∃ e : Edge x x,
      e.toHoHom = 𝟙 (HomotopyCategory.mk x : hoFunctor.obj X) :=
  Edge.exists_toHoHom_eq _

/-- A composition relation in the homotopy category of a
quasicategory lifts to a `CompStruct`. -/
example {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₀₂ : Edge x₀ x₂}
    (s : Edge.CompStruct e₀₁ e₁₂ e₀₂) :
    Nonempty (Edge.CompStruct e₀₁ e₁₂ e₀₂) :=
  Edge.nonempty_compStruct_of_toHoHom_comp_eq (Edge.toHoHom_comp s)

/-- Main converse: an equivalence edge in a quasicategory carries
inverse data. -/
example {e : Edge x₀ x₁} (h : e.IsEquivalence) :
    Nonempty e.InvStruct :=
  h.nonempty_invStruct

/-- Main converse, functional form. -/
example {e : Edge x₀ x₁} (h : e.IsEquivalence) :
    Nonempty e.InvStruct :=
  Edge.nonempty_invStruct_of_isEquivalence h

/-- The if-and-only-if characterization, as a statement. -/
example {e : Edge x₀ x₁} :
    e.IsEquivalence ↔ Nonempty e.InvStruct :=
  Edge.isEquivalence_iff_nonempty_invStruct

/-- Forward direction of the characterization, through the
if-and-only-if. -/
example {e : Edge x₀ x₁} (h : e.IsEquivalence) :
    Nonempty e.InvStruct :=
  Edge.isEquivalence_iff_nonempty_invStruct.mp h

/-- Backwards direction of the characterization, through the
if-and-only-if. -/
example {e : Edge x₀ x₁} (h : Nonempty e.InvStruct) :
    e.IsEquivalence :=
  Edge.isEquivalence_iff_nonempty_invStruct.mpr h

/-- The inverse edge of an equivalence, obtained from the produced
`InvStruct`, is itself an equivalence. -/
example {e : Edge x₀ x₁} (h : e.IsEquivalence) :
    ∃ e' : Edge x₁ x₀, e'.IsEquivalence := by
  obtain ⟨I⟩ := h.nonempty_invStruct
  exact ⟨I.inv, I.invStructInv.isEquivalence⟩

/-- The identity edge of a quasicategory carries inverse data,
obtained from its equivalence through the main converse. -/
example (x : X _⦋0⦌) : Nonempty (Edge.id x).InvStruct :=
  (Edge.isEquivalence_id x).nonempty_invStruct

/-- The identity edge carries inverse data obtained directly from
`InvStruct.invStructId`, agreeing with the converse output type. -/
example (x : X _⦋0⦌) : Nonempty (Edge.id x).InvStruct :=
  ⟨Edge.InvStruct.invStructId x⟩

/-- The identity edge is an equivalence through the backwards
direction of the characterization. -/
example (x : X _⦋0⦌) : (Edge.id x).IsEquivalence :=
  Edge.isEquivalence_iff_nonempty_invStruct.mpr
    ⟨Edge.InvStruct.invStructId x⟩

/-- A composite equivalence carries inverse data: compose two
equivalences along a `CompStruct`, then apply the main converse
to the composite. -/
example {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₀₂ : Edge x₀ x₂}
    (s : Edge.CompStruct e₀₁ e₁₂ e₀₂) (h₀₁ : e₀₁.IsEquivalence)
    (h₁₂ : e₁₂.IsEquivalence) : Nonempty e₀₂.InvStruct :=
  (Edge.IsEquivalence.of_compStruct s h₀₁ h₁₂).nonempty_invStruct

/-- Transport to another quasicategory preserves the conclusion:
the image of an equivalence under a simplicial map into a
quasicategory carries inverse data in the target. -/
example {Y : SSet.{u}} [Quasicategory Y]
    {e : Edge x₀ x₁} (h : e.IsEquivalence) (f : X ⟶ Y) :
    Nonempty (e.map f).InvStruct :=
  (h.map f).nonempty_invStruct

end QuasicategoryInvStruct

section CoherentIsoForwardTests

variable {X : SSet.{u}} {x₀ x₁ : X _⦋0⦌}

/-- Extension along the endpoint inclusion gives inverse data; here
the identity extension of the forward edge of `coherentIso`. -/
example : Nonempty (coherentIso.hom.{u}).InvStruct :=
  Edge.nonempty_invStruct_of_coherentIso_extension
    ⟨𝟙 coherentIso.{u}, by simp⟩

/-- Image form of the forward chain, with the identity map. -/
example : Nonempty (coherentIso.hom.{u}).InvStruct :=
  Edge.nonempty_invStruct_of_eq_map_coherentIso_hom
    (g := 𝟙 coherentIso.{u}) (by simp)

/-- An edge that is the image of `coherentIso.hom` under any map
carries inverse data, in image form. -/
example {e : Edge x₀ x₁} (g : coherentIso.{u} ⟶ X)
    (h : e.edge = g.app _ coherentIso.hom.edge) :
    Nonempty e.InvStruct :=
  Edge.nonempty_invStruct_of_eq_map_coherentIso_hom h

/-- The forward chain exercised through the extension form into
the equivalence conclusion. -/
example {e : Edge x₀ x₁}
    (h : ∃ g : coherentIso.{u} ⟶ X,
      SSet.yonedaEquiv.symm coherentIso.hom.edge ≫ g =
        SSet.yonedaEquiv.symm e.edge) :
    e.IsEquivalence := by
  obtain ⟨I⟩ := Edge.nonempty_invStruct_of_coherentIso_extension h
  exact I.isEquivalence

/-- In a quasicategory, an extension gives an equivalence whose
inverse data is then recovered by the main converse. -/
example [Quasicategory X] {e : Edge x₀ x₁}
    (h : ∃ g : coherentIso.{u} ⟶ X,
      SSet.yonedaEquiv.symm coherentIso.hom.edge ≫ g =
        SSet.yonedaEquiv.symm e.edge) :
    Nonempty e.InvStruct :=
  (Edge.isEquivalence_of_coherentIso_extension h).nonempty_invStruct

end CoherentIsoForwardTests

section NerveExtensionTests

variable {C : Type u} [Category.{v} C]

/-- Nerve extension gate, as an if-and-only-if statement. -/
example {x y : (CategoryTheory.nerve C) _⦋0⦌}
    (e : (CategoryTheory.nerve C).Edge x y) :
    e.IsEquivalence ↔
      ∃ g : coherentIso.{max u v} ⟶ CategoryTheory.nerve C,
        SSet.yonedaEquiv.symm coherentIso.hom.edge ≫ g =
          SSet.yonedaEquiv.symm e.edge :=
  Edge.isEquivalence_nerve_iff_coherentIso_extension e

/-- Forward direction: an equivalence edge in a nerve extends
along `Δ[1] ⟶ SSet.coherentIso`. -/
example {x y : (CategoryTheory.nerve C) _⦋0⦌}
    {e : (CategoryTheory.nerve C).Edge x y} (h : e.IsEquivalence) :
    ∃ g : coherentIso.{max u v} ⟶ CategoryTheory.nerve C,
      SSet.yonedaEquiv.symm coherentIso.hom.edge ≫ g =
        SSet.yonedaEquiv.symm e.edge :=
  h.exists_coherentIso_extension_nerve

/-- Backwards direction: a nerve edge with an extension is an
equivalence. -/
example {x y : (CategoryTheory.nerve C) _⦋0⦌}
    (e : (CategoryTheory.nerve C).Edge x y)
    (h : ∃ g : coherentIso.{max u v} ⟶ CategoryTheory.nerve C,
      SSet.yonedaEquiv.symm coherentIso.hom.edge ≫ g =
        SSet.yonedaEquiv.symm e.edge) :
    e.IsEquivalence :=
  (Edge.isEquivalence_nerve_iff_coherentIso_extension e).mpr h

/-- The edge of an isomorphism of `C` extends to `coherentIso`. -/
example {a b : C} (f : a ⟶ b) [IsIso f] :
    ∃ g : coherentIso.{max u v} ⟶ CategoryTheory.nerve C,
      SSet.yonedaEquiv.symm coherentIso.hom.edge ≫ g =
        SSet.yonedaEquiv.symm (CategoryTheory.nerve.edgeMk f).edge :=
  ((Edge.isEquivalence_nerve_edgeMk_iff f).mpr
    inferInstance).exists_coherentIso_extension_nerve

/-- An extension of `nerve.edgeMk f` forces `f` to be an
isomorphism, chaining the extension gate with the nerve gate. -/
example {a b : C} (f : a ⟶ b)
    (h : ∃ g : coherentIso.{max u v} ⟶ CategoryTheory.nerve C,
      SSet.yonedaEquiv.symm coherentIso.hom.edge ≫ g =
        SSet.yonedaEquiv.symm (CategoryTheory.nerve.edgeMk f).edge) :
    IsIso f :=
  (Edge.isEquivalence_nerve_edgeMk_iff f).mp
    ((Edge.isEquivalence_nerve_iff_coherentIso_extension _).mpr h)

/-- The identity morphism of `C` extends to `coherentIso`. -/
example (a : C) :
    ∃ g : coherentIso.{max u v} ⟶ CategoryTheory.nerve C,
      SSet.yonedaEquiv.symm coherentIso.hom.edge ≫ g =
        SSet.yonedaEquiv.symm
          (CategoryTheory.nerve.edgeMk (𝟙 a)).edge :=
  ((Edge.isEquivalence_nerve_edgeMk_iff (𝟙 a)).mpr
    inferInstance).exists_coherentIso_extension_nerve

/-- For nerves, inverse data for an equivalence edge also arises
from the extension: the built extension is fed through the
forward chain for arbitrary simplicial sets. -/
example {x y : (CategoryTheory.nerve C) _⦋0⦌}
    {e : (CategoryTheory.nerve C).Edge x y} (h : e.IsEquivalence) :
    Nonempty e.InvStruct :=
  Edge.nonempty_invStruct_of_coherentIso_extension
    h.exists_coherentIso_extension_nerve

end NerveExtensionTests

end EdgeEquivalenceInvTest
end MathlibExtTest.AlgebraicTopology.Quasicategory
