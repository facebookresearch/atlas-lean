/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.CartesianEdge.CancellationHorn
import MathlibExt.AlgebraicTopology.SimplicialSet.CartesianEdge.Fibration
import MathlibExt.AlgebraicTopology.SimplicialSet.CartesianEdge.Identity
import MathlibExt.AlgebraicTopology.SimplicialSet.CartesianEdge.InverseLift
import MathlibExt.AlgebraicTopology.SimplicialSet.CartesianEdge.RightHornCriterion
import MathlibExt.AlgebraicTopology.SimplicialSet.KanComplex.FundamentalGroupoid
import MathlibExt.AlgebraicTopology.SimplicialSet.NerveMax
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct

/-!
# Focused clients for Cartesian edges, Cartesian fibrations and maximum-level nerves

The right-horn criterion proves directly that every edge is Cartesian for an
identity map, and recovers the fillers from `isPCartesian_id`. The inverse lift
shows that the generating edge of the nerve of `Fin 2` is not Cartesian over any
Kan complex, and a Kan target exists. In a Kan complex every endomorphism that
cancels against an edge is the identity of the homotopy category. Identity maps
are Cartesian fibrations, and maximum-level nerve maps are evaluated on a chain
inclusion.
-/

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory Opposite
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.CartesianEdgeClientsTest

open SSet

/-- The right-horn criterion holds for an identity map: the base simplex is a filler. -/
example {X : SSet.{u}} (e : (Δ[1] : SSet.{u}) ⟶ X) :
    CartesianEdge.IsPCartesian (𝟙 X) e :=
  (CartesianEdge.isPCartesian_iff_rightHornLifting _ _).2 fun _ _ b h _ ↦
    ⟨b, by simpa using h.symm, by simp⟩

/-- Over an isomorphism every edge is Cartesian, so every critical right horn
over a base simplex lifts to a filler over that simplex. -/
example {X B : SSet.{u}} (p : X ⟶ B) [IsIso p] (e : (Δ[1] : SSet.{u}) ⟶ X) (n : ℕ)
    (σ₀ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{u}) ⟶ X) (b : (Δ[n + 2] : SSet.{u}) ⟶ B)
    (hb : σ₀ ≫ p = Λ[n + 2, Fin.last (n + 2)].ι ≫ b)
    (he : (SSet.rightHornEdge σ₀).edge = SSet.yonedaEquiv e) :
    ∃ σ : (Δ[n + 2] : SSet.{u}) ⟶ X, Λ[n + 2, Fin.last (n + 2)].ι ≫ σ = σ₀ ∧ σ ≫ p = b :=
  (CartesianEdge.isPCartesian_iff_rightHornLifting p e).1
    (CartesianEdge.isPCartesian_of_isIso p e) n σ₀ b hb he

/-- The generating `1`-simplex `0 ⟶ 1` of the nerve of `Fin 2`. -/
abbrev edge01 : (nerve (Fin 2)) _⦋1⦌ :=
  ComposableArrows.mk₁ (homOfLE (show (0 : Fin 2) ≤ 1 by decide))

/-- Over a Kan complex, the generating edge of the nerve of `Fin 2` is not
Cartesian: a lifted inverse triangle would give an arrow `1 ⟶ 0`. -/
theorem edge01_not_isPCartesian {T : SSet.{0}} [KanComplex T] (p : nerve (Fin 2) ⟶ T) :
    ¬ CartesianEdge.IsPCartesian p (SSet.yonedaEquiv.symm edge01) := fun h ↦ by
  obtain ⟨g, -, -⟩ :=
    CartesianEdge.exists_inverse_triangle p (Edge.mk' edge01) h (Edge.mk' edge01 |>.map p).invStruct
  exact absurd (leOfHom (nerve.homEquiv g)) (by decide)

/-- A Kan target for the previous guard exists. -/
example :
    ∃ (T : SSet.{0}) (_ : KanComplex T) (p : nerve (Fin 2) ⟶ T),
      ¬ CartesianEdge.IsPCartesian p (SSet.yonedaEquiv.symm edge01) :=
  ⟨(ihom (Δ[0] : SSet.{0})).obj (⊤_ SSet.{0}), inferInstance,
    MonoidalClosed.curry (terminal.from _), edge01_not_isPCartesian _⟩

/-- In a Kan complex, an endomorphism `h` with `h ≫ e = e` witnessed by a
triangle is the identity in the homotopy category. -/
example {X : SSet.{u}} [KanComplex X] {x y : X _⦋0⦌} {e : Edge x y} {h : Edge x x}
    (H : Edge.CompStruct h e e) :
    HomotopyCategory.homMk h = 𝟙 (HomotopyCategory.mk x : hoFunctor.obj X) := by
  obtain ⟨T, hT⟩ := KanComplex.hornFilling (CartesianEdge.cancellationHorn H)
  exact CartesianEdge.toHoHom_eq_id_of_cancellationHorn_fill H T hT.symm

/-- The critical edge of the cancellation horn is the edge being cancelled. -/
example {X : SSet.{u}} {x y : X _⦋0⦌} (e : Edge x y) :
    (SSet.rightHornEdge (CartesianEdge.cancellationHorn (Edge.CompStruct.idComp e))).edge =
      e.edge :=
  CartesianEdge.cancellationHorn_edge _

/-- Identity maps are Cartesian fibrations, hence inner fibrations. -/
example (X : SSet.{u}) : InnerFibration (𝟙 X) :=
  (CartesianFibration.identity X).toInnerFibration

/-- Identity maps are cocartesian fibrations. -/
example (X : SSet.{u}) : CocartesianFibration (𝟙 X) := CocartesianFibration.identity X

/-- The source of a Cartesian fibration over a quasicategory is a quasicategory. -/
example {X B : SSet.{u}} (p : X ⟶ B) [CartesianFibration p] [Quasicategory B] :
    Quasicategory X :=
  CartesianFibration.quasicategory_source p

/-- The inclusion of the chain `Fin 2` into `Fin 3`. -/
abbrev inclusion : Fin 2 ⥤ Fin 3 := Fin.castSuccOrderEmb.monotone.functor

/-- Maximum-level nerve maps read back the original objects in degree zero. -/
example :
    (NerveUniverses.nerveMapMax.{0, 0} inclusion).app (op ⦋0⦌) (ComposableArrows.mk₀ 1) =
      ComposableArrows.mk₀ (1 : Fin 3) :=
  NerveUniverses.nerveMapMax_app_mk₀ inclusion 1

/-- At equal universe levels the maximum-level nerve map is the ordinary one. -/
example : NerveUniverses.nerveMapMax.{0, 0} inclusion = nerveMap inclusion :=
  NerveUniverses.nerveMapMax_eq_nerveMap inclusion

/-- The functor is recovered from its maximum-level nerve map. -/
example :
    NerveUniverses.functorOfMapMax (NerveUniverses.nerveMapMax.{0, 0} inclusion) = inclusion :=
  NerveUniverses.functorOfMapMax_nerveMapMax inclusion

end MathlibExtTest.AlgebraicTopology.SimplicialSet.CartesianEdgeClientsTest
