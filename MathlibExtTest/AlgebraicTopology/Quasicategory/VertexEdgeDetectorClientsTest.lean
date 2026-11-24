/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Quasicategory.ColimitCone
import MathlibExt.AlgebraicTopology.Quasicategory.KanEdgeDetector
import MathlibExt.AlgebraicTopology.Quasicategory.NativePullback.Cone
import MathlibExt.AlgebraicTopology.Quasicategory.NerveTerminalVertex
import MathlibExt.AlgebraicTopology.Quasicategory.WideSubcategory.Basic

/-!
# Focused clients for quasicategory vertices, edge detection and wide subcategories

The clients evaluate the terminal-vertex criterion on the nerves of the chains
`Fin 3` and `Fin 2`, where it holds at the top and fails at the bottom. In the
nerve of `Fin 2` the generating edge is not an equivalence: it neither extends
over the Kan edge detector nor lies in the all-isomorphism wide subcomplex,
while identity edges do both. The cone criteria are used at an arbitrary cone.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.Quasicategory.VertexEdgeDetectorClientsTest

open SSet

/-- The generating `1`-simplex `0 ⟶ 1` of the nerve of `Fin 2`. -/
abbrev edge01 : (nerve (Fin 2)) _⦋1⦌ :=
  ComposableArrows.mk₁ (homOfLE (show (0 : Fin 2) ≤ 1 by decide))

/-- The generating edge of the nerve of `Fin 2` is not an equivalence:
an inverse would give `1 ≤ 0`. -/
theorem edge01_not_isEquivalence : ¬ (Edge.mk' edge01).IsEquivalence := by
  intro h
  have := (Edge.isEquivalence_nerve_iff (Edge.mk' edge01)).1 h
  have hle := leOfHom (inv (nerve.homEquiv (Edge.mk' edge01)))
  exact absurd hle (by decide)

/-- The top of `Fin 3` is a terminal vertex of its nerve. -/
example :
    IsTerminalVertex ((SSet.yonedaEquiv (X := nerve (Fin 3))).symm
      (ComposableArrows.mk₀ (⊤ : Fin 3))) :=
  isTerminalVertex_nerve_of_isTerminal isTerminalTop

/-- The bottom of `Fin 2` is not a terminal vertex of its nerve, since there
is no arrow `1 ⟶ 0`. -/
example :
    ¬ IsTerminalVertex ((SSet.yonedaEquiv (X := nerve (Fin 2))).symm
      (ComposableArrows.mk₀ (0 : Fin 2))) := by
  rw [isTerminalVertex_nerve_iff]
  rintro ⟨h⟩
  exact absurd (leOfHom (h.from (1 : Fin 2))) (by decide)

/-- The generating edge of the nerve of `Fin 2` does not extend over the Kan
edge detector. -/
example :
    ¬ ∃ g : KanEdgeDetector.object.{0} ⟶ nerve (Fin 2),
      KanEdgeDetector.edge ≫ g = SSet.yonedaEquiv.symm edge01 := fun h ↦
  edge01_not_isEquivalence ((KanEdgeDetector.isEquivalence_iff_extension edge01).2 h)

/-- Identity edges of a quasicategory extend over the Kan edge detector into
the core. -/
example {X : SSet.{u}} [Quasicategory X] (x : X _⦋0⦌) :
    ∃ g : KanEdgeDetector.object.{u} ⟶ (core X : SSet.{u}),
      KanEdgeDetector.edge.{u} ≫ g ≫ (core X).ι = SSet.yonedaEquiv.symm (Edge.id x).edge :=
  KanEdgeDetector.exists_core_extension (Edge.id x) (Edge.isEquivalence_id x)

/-- Every edge into a Kan complex extends over the detector. -/
example {X : SSet.{u}} [KanComplex X] (f : (Δ[1] : SSet.{u}) ⟶ X) :
    ∃ g : KanEdgeDetector.object.{u} ⟶ X, KanEdgeDetector.edge.{u} ≫ g = f :=
  KanEdgeDetector.exists_extension_into_kan f

/-- The isomorphism class of the homotopy category of the nerve of `Fin 2`. -/
abbrev isos : MorphismProperty (hoFunctor.obj (nerve (Fin 2))) :=
  MorphismProperty.isomorphisms _

/-- The all-isomorphism wide subcomplex keeps every vertex. -/
example : (Subcomplex.ofMorphismProperty isos).obj (op ⦋0⦌) = Set.univ :=
  Subcomplex.ofMorphismProperty_obj_zero isos

/-- The generating edge is not retained by the all-isomorphism wide subcomplex. -/
example : edge01 ∉ (Subcomplex.ofMorphismProperty isos).obj (op ⦋1⦌) := fun h ↦
  edge01_not_isEquivalence ((Subcomplex.mem_ofMorphismProperty_obj_one isos).1 h)

/-- Degenerate edges are retained by the all-isomorphism wide subcomplex. -/
example (x : (nerve (Fin 2)) _⦋0⦌) :
    (nerve (Fin 2)).σ (0 : Fin 1) x ∈ (Subcomplex.ofMorphismProperty isos).obj (op ⦋1⦌) :=
  (Subcomplex.mem_ofMorphismProperty_obj_one isos).2 (Subcomplex.property_degenerate isos x)

/-- The equivalence wide subcategory is the core, so it misses the generating edge. -/
example : edge01 ∉ (WideSubcategory.equivalences (nerve (Fin 2))).subcomplex.obj (op ⦋1⦌) := by
  rw [WideSubcategory.equivalences_subcomplex, mem_core_obj_one_iff]
  exact edge01_not_isEquivalence

/-- Every wide subcategory contains the core. -/
example {X : SSet.{u}} (W : WideSubcategory X) {s : X _⦋1⦌}
    (hs : (Edge.mk' s).IsEquivalence) : s ∈ W.subcomplex.obj (op ⦋1⦌) :=
  W.core_le _ ((mem_core_obj_one_iff).2 hs)

/-- A right cone is a colimit cone exactly when its cone point is initial in the
slice under its own base. -/
example {X K : SSet.{u}} (q : K ⋆ (Δ[0] : SSet.{u}) ⟶ X) :
    IsColimitCone q ↔ IsInitialVertex (sliceUnder.conePoint (joinInl K Δ[0] ≫ q) q rfl) :=
  isColimitCone_iff_isInitialVertex _ q rfl

/-- The cone point projects to the cone's apex. -/
example {X K : SSet.{u}} (q : K ⋆ (Δ[0] : SSet.{u}) ⟶ X) :
    sliceUnder.conePoint (joinInl K Δ[0] ≫ q) q rfl ≫
        sliceUnder.proj X (joinInl K Δ[0] ≫ q) = joinInr K Δ[0] ≫ q :=
  sliceUnder.conePoint_proj _ q rfl

/-- A square is a pullback square exactly when its cone point is terminal in the
slice over its cospan. -/
example {X : SSet.{u}} (q : NativePullback.squareShape.{u} ⟶ X) :
    NativePullback.IsPullbackSquare q ↔
      IsTerminalVertex (sliceOver.conePoint (NativePullback.cospanInclusion ≫ q)
        (NativePullback.coneDiagram q) (NativePullback.coneDiagram_fixed q)) :=
  NativePullback.isPullbackSquare_iff_isTerminalVertex q

end MathlibExtTest.AlgebraicTopology.Quasicategory.VertexEdgeDetectorClientsTest
