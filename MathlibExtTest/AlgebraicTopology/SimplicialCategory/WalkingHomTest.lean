/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialCategory.WalkingHom
import MathlibExt.AlgebraicTopology.SimplicialSet.GroupoidNerveKan

/-!
# Native consumers of the two-object simplicial enrichment

The tests preserve a higher scalar universe, empty reverse Hom, coincident
object images, and the entire fixed-object boundary-lift triangles. The actual
discrete two-point nerve exercises local Kan horn lifting and the boundary
restriction fibration. Its two distinct vertices cannot bound an interval,
so local Kan fibrancy does not imply arbitrary prescribed boundary existence.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory HomotopicalAlgebra SSet
open scoped Simplicial SSet.modelCategoryQuillen

namespace MathlibExtTest.AlgebraicTopology.SimplicialCategory.WalkingHomTest

noncomputable section

example (X : SSet.{2}) :
    ((WalkingHom.source : WalkingHom X) ⟶[SSet.{2}] WalkingHom.target) = X :=
  WalkingHom.hom_source_target X

example (X : SSet.{1}) (Δ : SimplexCategoryᵒᵖ)
    (x : ((WalkingHom.target : WalkingHom X) ⟶[SSet.{1}] WalkingHom.source).obj Δ) :
    False := PEmpty.elim x

-- The two chosen objects may coincide; a forward simplex then becomes a loop.
example :
    (WalkingHom.ofMap (WalkingHom.source : WalkingHom (Δ[1] : SSet.{1}))
      WalkingHom.source (toUnit (Δ[1] : SSet.{1}))).obj WalkingHom.target =
      WalkingHom.source := rfl

example :
    (WalkingHom.fixedObjectEquiv
      (WalkingHom.source : WalkingHom (Δ[1] : SSet.{1})) WalkingHom.source)
      ⟨WalkingHom.ofMap WalkingHom.source WalkingHom.source (toUnit (Δ[1] : SSet.{1})),
        rfl, rfl⟩ = toUnit (Δ[1] : SSet.{1}) := by
  change toUnit (Δ[1] : SSet.{1}) ≫ 𝟙 _ = toUnit (Δ[1] : SSet.{1})
  exact Category.comp_id _

-- A genuine original boundary family lift preserves both whole enriched functors.
example :
    ∃ L : WalkingHom.FixedObjects (X := (Δ[1] : SSet.{1}))
        (WalkingHom.source : WalkingHom (Δ[1] : SSet.{1})) WalkingHom.target,
      EnrichedFunctor.comp SSet.{1} (WalkingHom.map ∂Δ[1].ι) L.val =
        WalkingHom.map ∂Δ[1].ι ∧
      EnrichedFunctor.comp SSet.{1} L.val
        (EnrichedFunctor.id SSet.{1} (WalkingHom (Δ[1] : SSet.{1}))) =
        WalkingHom.map (𝟙 (Δ[1] : SSet.{1})) := by
  let P := EnrichedFunctor.id SSet.{1} (WalkingHom (Δ[1] : SSet.{1}))
  have hp : modelCategoryQuillen.I.rlp (P.map WalkingHom.source WalkingHom.target) := by
    intro A B i hi
    change HasLiftingProperty i (𝟙 (Δ[1] : SSet.{1}))
    infer_instance
  have sq : CommSq ∂Δ[1].ι ∂Δ[1].ι
      (P.map WalkingHom.source WalkingHom.target) (𝟙 (Δ[1] : SSet.{1})) :=
    ⟨by simp [P]⟩
  exact WalkingHom.exists_boundary_lift P WalkingHom.source WalkingHom.target hp 1 _ _ sq

/-- The actual two-component Kan Hom object. -/
abbrev twoPointNerve : SSet.{0} := nerve (Discrete Bool)

private instance : Groupoid (Discrete Bool) := Groupoid.ofIsGroupoid

private instance : KanComplex twoPointNerve := kanComplex_nerve_of_groupoid _

/-- The local Hom map discards the label while keeping the two enriched object positions. -/
def nerveProjection :
    EnrichedFunctor SSet.{0} (WalkingHom twoPointNerve) (WalkingHom (⊤_ SSet.{0})) :=
  WalkingHom.map (terminal.from twoPointNerve)

private instance : Fibration (nerveProjection.map WalkingHom.source WalkingHom.target) :=
  inferInstanceAs (Fibration (terminal.from twoPointNerve))

example : Fibration
    (WalkingHom.restrictionSquare nerveProjection WalkingHom.source WalkingHom.target
      ∂Δ[1].ι).π :=
  WalkingHom.boundaryRestriction_fibration nerveProjection WalkingHom.source WalkingHom.target 1

example (n : ℕ) (k : Fin (n + 2)) (f : (Λ[n + 1, k] : SSet.{0}) ⟶ twoPointNerve) :
    ∃ L : WalkingHom.FixedObjects (X := (Δ[n + 1] : SSet.{0}))
        (WalkingHom.source : WalkingHom twoPointNerve) WalkingHom.target,
      EnrichedFunctor.comp SSet.{0} (WalkingHom.map Λ[n + 1, k].ι) L.val =
        WalkingHom.ofMap WalkingHom.source WalkingHom.target f ∧
      EnrichedFunctor.comp SSet.{0} L.val nerveProjection =
        WalkingHom.map (terminal.from (Δ[n + 1] : SSet.{0})) := by
  have sq : CommSq f Λ[n + 1, k].ι
      (nerveProjection.map WalkingHom.source WalkingHom.target)
      (terminal.from (Δ[n + 1] : SSet.{0})) := ⟨by simp [nerveProjection]⟩
  exact WalkingHom.exists_horn_lift nerveProjection WalkingHom.source WalkingHom.target n k _ _ sq

/-- The two distinct original nerve vertices. -/
def vertex (b : Bool) : twoPointNerve _⦋0⦌ := ComposableArrows.mk₀ (Discrete.mk b)

-- A local Kan map permits horn extensions but cannot connect distinct components.
example : ¬ ∃ L : WalkingHom.FixedObjects (X := (Δ[1] : SSet.{0}))
      (WalkingHom.source : WalkingHom twoPointNerve) WalkingHom.target,
    EnrichedFunctor.comp SSet.{0} (WalkingHom.map (stdSimplex.δ (1 : Fin 2))) L.val =
      WalkingHom.ofMap WalkingHom.source WalkingHom.target (SSet.const (vertex false)) ∧
    EnrichedFunctor.comp SSet.{0} (WalkingHom.map (stdSimplex.δ (0 : Fin 2))) L.val =
      WalkingHom.ofMap WalkingHom.source WalkingHom.target (SSet.const (vertex true)) := by
  rintro ⟨L, h₀, h₁⟩
  let f : (Δ[1] : SSet.{0}) ⟶ twoPointNerve :=
    WalkingHom.fixedObjectEquiv WalkingHom.source WalkingHom.target L
  have hL : WalkingHom.ofMap WalkingHom.source WalkingHom.target f = L.val :=
    congrArg Subtype.val
      ((WalkingHom.fixedObjectEquiv WalkingHom.source WalkingHom.target).symm_apply_apply L)
  rw [← hL] at h₀ h₁
  have hc₀ :
      EnrichedFunctor.comp SSet.{0} (WalkingHom.map (stdSimplex.δ (1 : Fin 2)))
        (WalkingHom.ofMap WalkingHom.source WalkingHom.target f) =
      WalkingHom.ofMap WalkingHom.source WalkingHom.target (stdSimplex.δ (1 : Fin 2) ≫ f) :=
    WalkingHom.ofMap_comp (WalkingHom.source : WalkingHom (Δ[1] : SSet.{0}))
      WalkingHom.target (stdSimplex.δ (1 : Fin 2))
      (WalkingHom.ofMap WalkingHom.source WalkingHom.target f)
  have hc₁ :
      EnrichedFunctor.comp SSet.{0} (WalkingHom.map (stdSimplex.δ (0 : Fin 2)))
        (WalkingHom.ofMap WalkingHom.source WalkingHom.target f) =
      WalkingHom.ofMap WalkingHom.source WalkingHom.target (stdSimplex.δ (0 : Fin 2) ≫ f) :=
    WalkingHom.ofMap_comp (WalkingHom.source : WalkingHom (Δ[1] : SSet.{0}))
      WalkingHom.target (stdSimplex.δ (0 : Fin 2))
      (WalkingHom.ofMap WalkingHom.source WalkingHom.target f)
  have hf₀ : stdSimplex.δ (1 : Fin 2) ≫ f = SSet.const (vertex false) :=
    WalkingHom.ofMap_injective WalkingHom.source WalkingHom.target (hc₀.symm.trans h₀)
  have hf₁ : stdSimplex.δ (0 : Fin 2) ≫ f = SSet.const (vertex true) :=
    WalkingHom.ofMap_injective WalkingHom.source WalkingHom.target (hc₁.symm.trans h₁)
  have hs : twoPointNerve.δ (1 : Fin 2) (SSet.yonedaEquiv f) = vertex false := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, hf₀, SSet.yonedaEquiv_const]
  have ht : twoPointNerve.δ (0 : Fin 2) (SSet.yonedaEquiv f) = vertex true := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, hf₁, SSet.yonedaEquiv_const]
  let e : twoPointNerve.Edge (vertex false) (vertex true) := Edge.mk (SSet.yonedaEquiv f) hs ht
  have h : false = true := (nerve.homEquiv e).eq
  exact Bool.noConfusion h

end

end MathlibExtTest.AlgebraicTopology.SimplicialCategory.WalkingHomTest
