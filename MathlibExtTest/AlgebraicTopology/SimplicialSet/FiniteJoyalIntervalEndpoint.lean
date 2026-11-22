/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalEndpoint

/-!
# Finite Joyal Interval Endpoint
-/

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory MonoidalClosed SSet SSet.joyalInterval
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalEndpoint

variable {A B C : SSet.{u}}

/-- A public client retains the entire interval map and both complete
inverse triangles, with an arbitrary prescribed endpoint. -/
theorem fullPrescribedTriangles (i : A ⟶ B) [Mono i] [Quasicategory C]
    (ε : Fin 2) (T_A : A ⊗ joyalInterval ⟶ C) (c : B ⟶ C)
    (hε : (ρ_ A).inv ≫ (A ◁ unitPoint ε) ≫ T_A = i ≫ c) :
    ∃ T_B : B ⊗ joyalInterval ⟶ C,
      (i ▷ joyalInterval) ≫ T_B = T_A ∧
        (ρ_ B).inv ≫ (B ◁ unitPoint ε) ≫ T_B = c ∧
        (i ▷ Δ[2]) ≫ (B ◁ leftTriangle) ≫ T_B = (A ◁ leftTriangle) ≫ T_A ∧
        (i ▷ Δ[2]) ≫ (B ◁ rightTriangle) ≫ T_B = (A ◁ rightTriangle) ≫ T_A := by
  obtain ⟨T_B, hsource, hendpoint⟩ := exists_extension_of_mono i ε T_A c hε
  refine ⟨T_B, hsource, hendpoint, ?_, ?_⟩
  · rw [← Category.assoc, ← whisker_exchange, Category.assoc, hsource]
  · rw [← Category.assoc, ← whisker_exchange, Category.assoc, hsource]

/-- Class membership supplies the ordinary lifting instance for every
prescribed square, and both strict diagonal equations. -/
theorem strictEndpointLift (i : A ⟶ B) [Mono i] [Quasicategory C]
    (ε : Fin 2) (a : A ⟶ (ihom joyalInterval).obj C) (c : B ⟶ C)
    (sq : CommSq a i (endpointEvaluation C ε) c) :
    ∃ g : B ⟶ (ihom joyalInterval).obj C,
      i ≫ g = a ∧ g ≫ endpointEvaluation C ε = c := by
  have : HasLiftingProperty i (endpointEvaluation C ε) :=
    endpointEvaluation_mem_rlp_monomorphisms C ε i (by infer_instance)
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

/-- Dimension zero includes the actual empty boundary. The per-map API
supplies a strict lift for either prescribed endpoint. -/
theorem boundaryZero [Quasicategory C] (ε : Fin 2)
    (a : (∂Δ[0] : SSet.{u}) ⟶ (ihom joyalInterval).obj C) (c : Δ[0] ⟶ C)
    (sq : CommSq a ∂Δ[0].ι (endpointEvaluation C ε) c) :
    ∃ g : Δ[0] ⟶ (ihom joyalInterval).obj C,
      ∂Δ[0].ι ≫ g = a ∧ g ≫ endpointEvaluation C ε = c := by
  have : HasLiftingProperty ∂Δ[0].ι (endpointEvaluation C ε) :=
    hasLiftingProperty_endpointEvaluation ∂Δ[0].ι ε
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

end MathlibExtTest.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalEndpoint
