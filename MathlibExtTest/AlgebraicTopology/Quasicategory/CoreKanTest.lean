/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.Quasicategory.CoreKan
public import Mathlib.AlgebraicTopology.Quasicategory.Nerve

/-!
# Tests for special outer horns and Kan-ness of the core

Public clients exercise the inner-horn filler for quasicategories in
compatible-family form, the distinguished-edge extraction for outer
horns and its interaction with the core, special outer horn filling
in dimension `2` in edge and in horn form (checked concretely in a
nerve, where the produced missing edge is identified in the
category), the special-filling predicate, the conditional Kan-ness
of the core, and the unconditional Kan-ness of the core of a Kan
complex. Only public declarations are used.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory Opposite
open scoped Simplicial

universe v u

namespace MathlibExtTest.AlgebraicTopology.Quasicategory
namespace CoreKanTest

open SSet

section Signatures

#check @SSet.horn.IsCompatible.exists_lift_of_quasicategory
#check @SSet.horn.IsCompatible.liftOfQuasicategory
#check @SSet.horn.IsCompatible.δ_liftOfQuasicategory
#check @SSet.leftHornEdgeSimplex
#check @SSet.rightHornEdgeSimplex
#check @SSet.leftHornEdge
#check @SSet.leftHornEdge_edge
#check @SSet.rightHornEdge
#check @SSet.rightHornEdge_edge
#check @SSet.leftHornEdge_isEquivalence_of_factor_core
#check @SSet.rightHornEdge_isEquivalence_of_factor_core
#check @SSet.Edge.exists_compStruct_of_isEquivalence_left
#check @SSet.Edge.exists_compStruct_of_isEquivalence_right
#check @SSet.exists_fill_horn_two_zero_of_isEquivalence
#check @SSet.exists_fill_horn_two_last_of_isEquivalence
#check @SSet.HasSpecialOuterHornFilling
#check @SSet.HasSpecialOuterHornFilling.left
#check @SSet.HasSpecialOuterHornFilling.right
#check @SSet.hasSpecialOuterHornFilling_of_kanComplex
#check @SSet.kanComplex_core_of_special_horn_filling
#check @SSet.kanComplex_core_of_kanComplex

end Signatures

section InnerFiller

variable {X : SSet.{u}} [Quasicategory X] {n : ℕ} {i : Fin (n + 2)}
  {f : ∀ (j : Fin (n + 2)) (_ : j ≠ i), Δ[n] ⟶ X}

/-- A quasicategory fills an inner horn given as a compatible
family of face maps. -/
example (h0 : 0 < i) (hn : i < Fin.last (n + 1))
    (hf : horn.IsCompatible f) :
    ∃ (φ : Δ[n + 1] ⟶ X),
      ∀ (j : Fin (n + 2)) (hj : j ≠ i), stdSimplex.δ j ≫ φ = f j hj :=
  hf.exists_lift_of_quasicategory h0 hn

/-- The chosen quasicategory filler has the prescribed faces. -/
example (h0 : 0 < i) (hn : i < Fin.last (n + 1))
    (hf : horn.IsCompatible f) (j : Fin (n + 2)) (hj : j ≠ i) :
    stdSimplex.δ j ≫ hf.liftOfQuasicategory h0 hn = f j hj :=
  hf.δ_liftOfQuasicategory h0 hn j hj

end InnerFiller

section HornEdges

variable {X : SSet.{u}} {n : ℕ}

/-- The underlying `1`-simplex of the first edge of a left outer
horn is the image of `leftHornEdgeSimplex`. -/
example (σ₀ : (Λ[n + 2, (0 : Fin (n + 3))] : SSet.{u}) ⟶ X) :
    (leftHornEdge σ₀).edge = σ₀.app _ (leftHornEdgeSimplex.{u} n) :=
  leftHornEdge_edge σ₀

/-- The underlying `1`-simplex of the last edge of a right outer
horn is the image of `rightHornEdgeSimplex`. -/
example (σ₀ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{u}) ⟶ X) :
    (rightHornEdge σ₀).edge = σ₀.app _ (rightHornEdgeSimplex.{u} n) :=
  rightHornEdge_edge σ₀

/-- The first edge of a left outer horn that factors through the
core is an equivalence. -/
example (τ : (Λ[n + 2, (0 : Fin (n + 3))] : SSet.{u}) ⟶
    (core X : SSet.{u})) :
    (leftHornEdge (τ ≫ (core X).ι)).IsEquivalence :=
  leftHornEdge_isEquivalence_of_factor_core τ

/-- The last edge of a right outer horn that factors through the
core is an equivalence. -/
example (τ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{u}) ⟶
    (core X : SSet.{u})) :
    (rightHornEdge (τ ≫ (core X).ι)).IsEquivalence :=
  rightHornEdge_isEquivalence_of_factor_core τ

end HornEdges

section TwoDimensional

variable {X : SSet.{u}} [Quasicategory X] {x₀ x₁ x₂ : X _⦋0⦌}

/-- Edge form of `Λ[2, 0]` filling: an equivalence first edge and a
long edge complete to a `2`-simplex. -/
example {e₀₁ : Edge x₀ x₁} (h : e₀₁.IsEquivalence)
    (e₀₂ : Edge x₀ x₂) :
    ∃ e₁₂ : Edge x₁ x₂, Nonempty (Edge.CompStruct e₀₁ e₁₂ e₀₂) :=
  Edge.exists_compStruct_of_isEquivalence_left h e₀₂

/-- Edge form of `Λ[2, 2]` filling: an equivalence last edge and a
long edge complete to a `2`-simplex. -/
example {e₁₂ : Edge x₁ x₂} (h : e₁₂.IsEquivalence)
    (e₀₂ : Edge x₀ x₂) :
    ∃ e₀₁ : Edge x₀ x₁, Nonempty (Edge.CompStruct e₀₁ e₁₂ e₀₂) :=
  Edge.exists_compStruct_of_isEquivalence_right h e₀₂

/-- With identity first edge, the missing edge exists for every
long edge of a quasicategory. -/
example (e : Edge x₀ x₂) :
    ∃ e₁₂ : Edge x₀ x₂,
      Nonempty (Edge.CompStruct (Edge.id x₀) e₁₂ e) :=
  Edge.exists_compStruct_of_isEquivalence_left
    (Edge.isEquivalence_id x₀) e

/-- Horn form of `Λ[2, 0]` filling in a quasicategory. -/
example (σ₀ : (Λ[2, (0 : Fin 3)] : SSet.{u}) ⟶ X)
    (h : (leftHornEdge σ₀).IsEquivalence) :
    ∃ σ : Δ[2] ⟶ X, σ₀ = Λ[2, (0 : Fin 3)].ι ≫ σ :=
  exists_fill_horn_two_zero_of_isEquivalence σ₀ h

/-- Horn form of `Λ[2, 2]` filling in a quasicategory. -/
example (σ₀ : (Λ[2, Fin.last 2] : SSet.{u}) ⟶ X)
    (h : (rightHornEdge σ₀).IsEquivalence) :
    ∃ σ : Δ[2] ⟶ X, σ₀ = Λ[2, Fin.last 2].ι ≫ σ :=
  exists_fill_horn_two_last_of_isEquivalence σ₀ h

/-- A horn of the core in dimension `2` on the left fills in `X`:
its first edge is an equivalence because it factors through the
core (no quasicategory hypothesis is used for the edge statement;
the filler uses it). -/
example (τ : (Λ[2, (0 : Fin 3)] : SSet.{u}) ⟶ (core X : SSet.{u})) :
    ∃ σ : Δ[2] ⟶ X, (τ ≫ (core X).ι) = Λ[2, (0 : Fin 3)].ι ≫ σ :=
  exists_fill_horn_two_zero_of_isEquivalence _
    (leftHornEdge_isEquivalence_of_factor_core τ)

end TwoDimensional

section NerveGate

variable {C : Type u} [Category.{v} C] {a b c : C}

/-- In a nerve, the edge produced by left special filling from an
isomorphism `f` and the long edge `f ≫ g` is the edge of `g`:
cancelling the isomorphism `f` in
`f ≫ homEquiv e₁₂ = f ≫ g` identifies it. -/
example (f : a ⟶ b) [IsIso f] (g : b ⟶ c) :
    ∃ e₁₂ : (nerve C).Edge (nerveEquiv.symm b) (nerveEquiv.symm c),
      nerve.homEquiv e₁₂ = g ∧
        Nonempty (Edge.CompStruct (nerve.edgeMk f) e₁₂
          (nerve.edgeMk (f ≫ g))) := by
  have hf : (nerve.edgeMk f).IsEquivalence :=
    (Edge.isEquivalence_nerve_edgeMk_iff f).mpr inferInstance
  obtain ⟨e₁₂, ⟨hc⟩⟩ :=
    Edge.exists_compStruct_of_isEquivalence_left hf
      (nerve.edgeMk (f ≫ g))
  refine ⟨e₁₂, ?_, ⟨hc⟩⟩
  have hcomp := nerve.homEquiv_comp hc
  rw [nerve.homEquiv_edgeMk, nerve.homEquiv_edgeMk] at hcomp
  exact (cancel_epi f).mp hcomp

/-- In a nerve, the edge produced by right special filling from
the long edge `f ≫ g` and an isomorphism `g` is the edge of `f`:
cancelling the isomorphism `g` in
`homEquiv e₀₁ ≫ g = f ≫ g` identifies it. -/
example (f : a ⟶ b) (g : b ⟶ c) [IsIso g] :
    ∃ e₀₁ : (nerve C).Edge (nerveEquiv.symm a) (nerveEquiv.symm b),
      nerve.homEquiv e₀₁ = f ∧
        Nonempty (Edge.CompStruct e₀₁ (nerve.edgeMk g)
          (nerve.edgeMk (f ≫ g))) := by
  have hg : (nerve.edgeMk g).IsEquivalence :=
    (Edge.isEquivalence_nerve_edgeMk_iff g).mpr inferInstance
  obtain ⟨e₀₁, ⟨hc⟩⟩ :=
    Edge.exists_compStruct_of_isEquivalence_right hg
      (nerve.edgeMk (f ≫ g))
  refine ⟨e₀₁, ?_, ⟨hc⟩⟩
  have hcomp := nerve.homEquiv_comp hc
  rw [nerve.homEquiv_edgeMk, nerve.homEquiv_edgeMk] at hcomp
  exact (cancel_mono g).mp hcomp

end NerveGate

section CoreKan

variable {X : SSet.{u}}

/-- A Kan complex has special outer horn filling. -/
example [KanComplex X] : HasSpecialOuterHornFilling X :=
  hasSpecialOuterHornFilling_of_kanComplex X

/-- Both components of the special filling property of a Kan
complex, applied to a horn factoring through its core. -/
example [KanComplex X] {n : ℕ}
    (τ : (Λ[n + 2, (0 : Fin (n + 3))] : SSet.{u}) ⟶
      (core X : SSet.{u})) :
    ∃ σ : Δ[n + 2] ⟶ X,
      (τ ≫ (core X).ι) = Λ[n + 2, (0 : Fin (n + 3))].ι ≫ σ :=
  (hasSpecialOuterHornFilling_of_kanComplex X).left _
    (leftHornEdge_isEquivalence_of_factor_core τ)

/-- Conditional Kan-ness of the core, applied. -/
example [Quasicategory X] (hsp : HasSpecialOuterHornFilling X) :
    KanComplex (core X : SSet.{u}) :=
  kanComplex_core_of_special_horn_filling hsp

/-- The core of a Kan complex is a Kan complex, by name. -/
example [KanComplex X] : KanComplex (core X : SSet.{u}) :=
  kanComplex_core_of_kanComplex X

/-- The core of a Kan complex is a Kan complex, by instance
search. -/
example [KanComplex X] : KanComplex (core X : SSet.{u}) :=
  inferInstance

/-- In particular, the core of a Kan complex fills all of its
outer horns. -/
example [KanComplex X] {n : ℕ} {i : Fin (n + 2)}
    (σ₀ : (Λ[n + 1, i] : SSet.{u}) ⟶ (core X : SSet.{u})) :
    ∃ σ : Δ[n + 1] ⟶ (core X : SSet.{u}),
      σ₀ = Λ[n + 1, i].ι ≫ σ :=
  KanComplex.hornFilling σ₀

/-- The core of a Kan complex is also a quasicategory, through its
Kan structure (and independently by the inner-fibration instance
of `Core.lean`). -/
example [KanComplex X] : Quasicategory (core X : SSet.{u}) :=
  inferInstance

/-- The core of a nerve equipped with a Kan complex instance (for
instance the nerve of a groupoid) is a Kan complex. -/
example {C : Type u} [Category.{v} C] [KanComplex (nerve C)] :
    KanComplex (core (nerve C) : SSet) :=
  kanComplex_core_of_kanComplex _

end CoreKan

end CoreKanTest
end MathlibExtTest.AlgebraicTopology.Quasicategory
