/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.HoFunctorTrivialFibration

@[expose] public section

/-!
# Trivial Kan fibration / homotopy-category client test

Downstream client for
`SSet.mapHomotopyCategory_isEquivalence_of_rlp_I`. The identity of
`Δ[2]` is a trivial Kan fibration, and the edge- and `2`-simplex lifting
lemmas applied to it recover the original simplices (the identity edge
of `Δ[1]` viewed in `Δ[2]`, and the identity `2`-simplex of `Δ[2]`
through the `CompStruct` determined by its faces), which distinguishes
the genuine boundary-lifting construction from a stub. The abstract
consequences (fullness, faithfulness, essential surjectivity, and the
bundled `Cat` form) are exercised for a general map `p` with
`modelCategoryQuillen.I.rlp p`.
-/

set_option autoImplicit false

open CategoryTheory Opposite

open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.HoFunctorTrivialFibrationTest

/-- The identity of `Δ[2]` has the right lifting property against the
generating cofibrations. -/
lemma rlp_id_delta_two :
    SSet.modelCategoryQuillen.I.rlp (𝟙 (Δ[2] : SSet.{0})) := by
  intro _ _ _ _
  infer_instance

/-- The main theorem applied to the identity: the identity functor on
the homotopy category of `Δ[2]`, presented as `mapHomotopyCategory (𝟙 _)`,
is an equivalence. -/
example : (SSet.mapHomotopyCategory (𝟙 (Δ[2] : SSet.{0}))).IsEquivalence :=
  SSet.mapHomotopyCategory_isEquivalence_of_rlp_I rlp_id_delta_two

/-- A strict section of the identity exists, as promised by the
section lemma. -/
example : ∃ s : (Δ[2] : SSet.{0}) ⟶ Δ[2], s ≫ 𝟙 (Δ[2] : SSet.{0}) = 𝟙 Δ[2] :=
  SSet.exists_section_of_rlp_I rlp_id_delta_two

/-- The fundamental `1`-simplex of `Δ[2]` given by the face map
`δ₂ : ⦋1⦌ ⟶ ⦋2⦌` (the edge `0 → 1`). -/
def edgeSimplex : (Δ[2] : SSet.{0}) _⦋1⦌ :=
  SSet.stdSimplex.objEquiv.symm (SimplexCategory.δ (2 : Fin 3))

/-- Edge lifting along the identity recovers the original
`1`-simplex. -/
example : ∃ e : SSet.Edge ((Δ[2] : SSet.{0}).δ 1 edgeSimplex)
      ((Δ[2] : SSet.{0}).δ 0 edgeSimplex), e.edge = edgeSimplex := by
  obtain ⟨e, he⟩ := SSet.exists_edge_lift_of_rlp_I rlp_id_delta_two rfl rfl
    (SSet.Edge.mk' edgeSimplex)
  exact ⟨e, he⟩

/-- The identity `2`-simplex of `Δ[2]`. -/
def twoSimplex : (Δ[2] : SSet.{0}) _⦋2⦌ :=
  SSet.stdSimplex.objEquiv.symm (𝟙 ⦋2⦌)

/-- `2`-simplex lifting along the identity recovers the identity
`2`-simplex from the `CompStruct` formed by its faces. -/
example : ∃ (x₀ x₁ x₂ : (Δ[2] : SSet.{0}) _⦋0⦌)
    (e₀₁ : SSet.Edge x₀ x₁) (e₁₂ : SSet.Edge x₁ x₂) (e₀₂ : SSet.Edge x₀ x₂)
    (h : SSet.Edge.CompStruct e₀₁ e₁₂ e₀₂), h.simplex = twoSimplex := by
  obtain ⟨x₀, x₁, x₂, e₀₁, e₁₂, e₀₂, h₀, hh₀⟩ :=
    SSet.Edge.CompStruct.exists_of_simplex twoSimplex
  obtain ⟨h, hh⟩ := SSet.exists_compStruct_lift_of_rlp_I (e₀₁ := e₀₁)
    (e₁₂ := e₁₂) (e₀₂ := e₀₂) rlp_id_delta_two
    twoSimplex (by simp [← hh₀]) (by simp [← hh₀]) (by simp [← hh₀])
  exact ⟨x₀, x₁, x₂, e₀₁, e₁₂, e₀₂, h, by simpa using hh⟩

section Abstract

variable {X Y : SSet.{0}} {p : X ⟶ Y} (hp : SSet.modelCategoryQuillen.I.rlp p)

/-- Essential surjectivity for a general trivial Kan fibration. -/
example : (SSet.mapHomotopyCategory p).EssSurj :=
  SSet.mapHomotopyCategory_essSurj_of_rlp_I hp

/-- Fullness for a general trivial Kan fibration. -/
example : (SSet.mapHomotopyCategory p).Full :=
  SSet.mapHomotopyCategory_full_of_rlp_I hp

/-- Faithfulness for a general trivial Kan fibration. -/
example : (SSet.mapHomotopyCategory p).Faithful :=
  SSet.mapHomotopyCategory_faithful_of_rlp_I hp

/-- The bundled `Cat` morphism `hoFunctor.map p` is an equivalence. -/
example : (SSet.hoFunctor.map p).toFunctor.IsEquivalence :=
  SSet.hoFunctor_map_isEquivalence_of_rlp_I hp

/-- Every vertex of `Y` lifts to `X`. -/
example (y : Y _⦋0⦌) : ∃ x : X _⦋0⦌, p.app (op ⦋0⦌) x = y :=
  SSet.exists_vertex_lift_of_rlp_I hp y

/-- The monomorphism form of the hypothesis gives the same conclusion. -/
example (hp' : (MorphismProperty.monomorphisms SSet.{0}).rlp p) :
    (SSet.mapHomotopyCategory p).IsEquivalence :=
  SSet.mapHomotopyCategory_isEquivalence_of_rlp_monomorphisms hp'

end Abstract

section AbstractUniverse

variable {X Y : SSet.{u}} {p : X ⟶ Y} (hp : SSet.modelCategoryQuillen.I.rlp p)

/-- The main equivalence result at a general universe. -/
example : (SSet.mapHomotopyCategory p).IsEquivalence :=
  SSet.mapHomotopyCategory_isEquivalence_of_rlp_I hp

/-- The bundled `Cat` form at a general universe. -/
example : (SSet.hoFunctor.map p).toFunctor.IsEquivalence :=
  SSet.hoFunctor_map_isEquivalence_of_rlp_I hp

/-- The monomorphism hypothesis form at a general universe. -/
example (hp' : (MorphismProperty.monomorphisms SSet.{u}).rlp p) :
    (SSet.mapHomotopyCategory p).IsEquivalence :=
  SSet.mapHomotopyCategory_isEquivalence_of_rlp_monomorphisms hp'

end AbstractUniverse

end MathlibExtTest.AlgebraicTopology.SimplicialSet.HoFunctorTrivialFibrationTest
