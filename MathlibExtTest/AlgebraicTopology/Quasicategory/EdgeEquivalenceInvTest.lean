/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

import Mathlib.AlgebraicTopology.Quasicategory.Nerve
import MathlibExt.AlgebraicTopology.Quasicategory.EdgeEquivalenceInv

/-!
# Clients of the equivalence-edge inverse bridge

The original Formal-Math tests are by Tsutomu Okano and Avocado.
-/

open CategoryTheory SSet
open scoped Simplicial SimplicialObject.Truncated

universe u

section QuotientComparison

variable {V : Truncated.{u} 2} [Truncated.Quasicategory₂ V]
  {a b c : V _⦋0⦌₂}

-- Compress a genuine two-edge path; no composition triangle is assumed.
example (e₁ : Truncated.Edge a b) (e₂ : Truncated.Edge b c) :
    ∃ e : Truncated.Edge a c,
      Truncated.HomotopyCategory.homMk e =
        Truncated.HomotopyCategory.homMk e₁ ≫ Truncated.HomotopyCategory.homMk e₂ :=
  Truncated.HomotopyCategory.exists_homMk_eq _

-- The other round trip fixes an arbitrary morphism of the edge quotient.
example {x y : Truncated.HomotopyCategory₂ V} (g : x ⟶ y) :
    Truncated.HomotopyCategory.toHomotopyCategory₂.map
        (Truncated.HomotopyCategory₂.toHomotopyCategory.map g) = g :=
  Truncated.HomotopyCategory.toHomotopyCategory₂_map_toHomotopyCategory_map g

end QuotientComparison

section Nerves

private def boolFlip : Bool ≅ Bool :=
  ({ toFun := Bool.not, invFun := Bool.not, left_inv := Bool.not_not,
     right_inv := Bool.not_not } : Bool ≃ Bool).toIso

private def flipEdge : (nerve (Type)).Edge (nerveEquiv.symm Bool) (nerveEquiv.symm Bool) :=
  nerve.edgeMk boolFlip.hom

example : boolFlip.hom ≠ 𝟙 Bool := by
  intro h
  have hf := ConcreteCategory.congr_hom h false
  change true = false at hf
  cases hf

private theorem flipEquivalence : flipEdge.IsEquivalence :=
  (Edge.isEquivalence_nerve_edgeMk_iff boolFlip.hom).mpr inferInstance

-- Inverse triangles exist for the Boolean flip; the input is a concrete category isomorphism.
example : Nonempty flipEdge.InvStruct :=
  flipEquivalence.nonempty_invStruct

-- The same nonidentity edge extends to the walking isomorphism in the actual nerve.
example : ∃ g : coherentIso ⟶ nerve (Type),
    SSet.yonedaEquiv.symm coherentIso.hom.edge ≫ g = SSet.yonedaEquiv.symm flipEdge.edge :=
  flipEquivalence.exists_coherentIso_extension_nerve

private def directedArrow : (0 : Fin 2) ⟶ 1 := homOfLE (by decide)

-- The edge of the noninvertible arrow has no coherence extension: an inverse would run 1 → 0.
example : ¬ ∃ g : coherentIso ⟶ nerve (Fin 2),
    SSet.yonedaEquiv.symm coherentIso.hom.edge ≫ g =
      SSet.yonedaEquiv.symm (nerve.edgeMk directedArrow).edge := by
  rw [← Edge.isEquivalence_nerve_iff_coherentIso_extension (nerve.edgeMk directedArrow),
    Edge.isEquivalence_nerve_edgeMk_iff]
  intro h
  obtain ⟨back, _, _⟩ := h.out
  exact (by decide : ¬ ((1 : Fin 2) ≤ 0)) (leOfHom back)

end Nerves
