/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual finite-index consequence of the complete original-source coset derivation. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTCIndexCorrectedRecognition
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTCIndexTargets
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationFiniteCoverFiniteness
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationE7Order

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Every finite target transition equation holds in the original C322 source group. -/
theorem y322TCIndexTransitionEquation_valid (i : Fin 3159) (g : Fin 8) :
    (y322TCIndexTransitionEquation i g).Valid
      (y322FiniteAuxiliaryValue y322TransportProgram) := by
  have h := y322TCIndexTarget_shape i g
  exact y322WordEquation_transport _ _ _
    (y322TCIndexCorrectedEquations_valid (y322TCIndexEdgeAt i g).equation) h.1 h.2

/-- A numbered positive original source generator retains its exact actual group value. -/
theorem y322TCIndexGenerator_value (g : Fin 8) :
    y322EquationWordValue (y322FiniteAuxiliaryValue y322TransportProgram)
      [(g.castAdd 48640, true)] = (PresentedGroup.of g : Y322Presentation) := by
  unfold y322EquationWordValue
  rw [FreeGroup.lift_mk]
  simp only [List.map_cons, List.map_nil, Bool.cond_true, List.prod_cons, List.prod_nil, mul_one]
  exact y322FiniteAuxiliaryValue_number y322TransportProgram (.inl g)

/-- Each exact finite table edge is an actual source-group equality with its E7 coefficient. -/
theorem y322TCIndexTransition (i : Fin 3159) (g : Fin 8) :
    y322TCIndexRepresentative i * PresentedGroup.of g =
      y322EquationWordValue (y322FiniteAuxiliaryValue y322TransportProgram)
        (y322TCIndexCoefficientWord i g) *
          y322TCIndexRepresentative (y322TCIndexEdgeAt i g).target := by
  have h := y322TCIndexTransitionEquation_valid i g
  change y322EquationWordValue _
      (y322TCIndexRepresentativeWord i ++ [(g.castAdd 48640, true)]) =
    y322EquationWordValue _ (y322TCIndexCoefficientWord i g ++
      y322TCIndexRepresentativeWord (y322TCIndexEdgeAt i g).target) at h
  simpa only [y322EquationWordValue_append, y322TCIndexRepresentativeWord_value,
    y322TCIndexGenerator_value] using h

/-- All actual source generator transitions have a genuine E7 coefficient and finite target. -/
theorem y322TCIndex_step (i : Fin 3159) (g : Fin 8) :
    ∃ h ∈ y322E7Parabolic, ∃ j : Fin 3159,
      y322TCIndexRepresentative i * PresentedGroup.of g = h * y322TCIndexRepresentative j :=
  ⟨_, y322TCIndexCoefficientWord_mem i g, _, y322TCIndexTransition i g⟩

/-- The complete literal source certificate covers every actual original C322 element. -/
theorem y322TCIndex_cover (g : Y322Presentation) :
    ∃ h ∈ y322E7Parabolic, ∃ i : Fin 3159, g = h * y322TCIndexRepresentative i :=
  y322Presentation_finite_cover y322E7Parabolic y322TCIndexRepresentative 0
    y322TCIndexRepresentative_zero y322TCIndex_step g

/-- The original E7 source subgroup has actual finite index in the original C322 presentation. -/
theorem y322E7Parabolic_finiteIndex : y322E7Parabolic.FiniteIndex :=
  y322Presentation_finiteIndex_of_cover y322E7Parabolic y322TCIndexRepresentative
    y322TCIndex_cover

/-- Its actual index is at most the 3159 verified original-source representatives. -/
theorem y322E7Parabolic_index_le : y322E7Parabolic.index ≤ 3159 :=
  y322Presentation_index_le_of_cover y322E7Parabolic y322TCIndexRepresentative y322TCIndex_cover

/-- The complete source cover and checked E7 bound prove actual C322 finiteness and order bound. -/
theorem y322Presentation_finite_card :
    Finite Y322Presentation ∧ Nat.card Y322Presentation ≤ 9170703360 := by
  let := y322E7Parabolic_finite
  let f : y322E7Parabolic × Fin 3159 → Y322Presentation :=
    fun x => x.1.val * y322TCIndexRepresentative x.2
  have hs : Function.Surjective f := by
    intro g
    obtain ⟨h, hh, i, hi⟩ := y322TCIndex_cover g
    exact ⟨(⟨h, hh⟩, i), hi.symm⟩
  refine ⟨Finite.of_surjective f hs, ?_⟩
  have hc : Nat.card Y322Presentation ≤ Nat.card y322E7Parabolic * 3159 := by
    simpa only [Nat.card_prod, Nat.card_fin] using Nat.card_le_card_of_surjective f hs
  exact hc.trans (Nat.mul_le_mul_right 3159 y322E7Parabolic_card_le)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
