/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionBinary
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationPhaseSeparation
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1BinaryInvariantQuadratics

/-! The genuine binary Ω orbit consists of nonzero singular classes with
actual norm-eight representatives. Short-vector roots are therefore excluded. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Every actual Ω orbit point has a genuine integral norm-eight representative. -/
theorem generatedAxisGlobalBinary_norm_eight (x : generatedAxisGlobalBinaryOrbit) :
    ∃ u : leechIntegral, leechSquareSum u.val = 64 ∧
      leechHyperbolicCoordinates (leechReduction u) = x.val := by
  obtain ⟨c, hc⟩ := x.property
  induction c using QuotientGroup.induction_on with
  | H e =>
    refine ⟨leechIntegralAction e (leechCoordinateFrameLattice 0), ?_, ?_⟩
    · rw [leechIntegralAction_squareSum]
      exact leechCoordinateFrameVector_square 0
    · change leechBinaryAction e (toAdd (qQuotHom sourceOmegaQ)) = x.val at hc
      rw [sourceOmegaQ_eq_frame_class, leechBinaryAction_coordinates] at hc
      exact hc

/-- No norm-four Leech class belongs to the actual norm-eight Ω orbit. -/
theorem generatedAxisGlobalBinary_short_excluded (u : leechIntegral)
    (hu : leechSquareSum u.val = 32) :
    leechHyperbolicCoordinates (leechReduction u) ∉ generatedAxisGlobalBinaryOrbit := by
  intro h
  obtain ⟨v, hv, he⟩ := generatedAxisGlobalBinary_norm_eight ⟨_, h⟩
  exact generatedAxis_short_norm_eight_class_ne u v hu hv
    (leechHyperbolicCoordinates.injective he.symm)

/-- The genuine Ω orbit excludes zero, since its Conway action is invertible. -/
theorem generatedAxisGlobalBinary_ne_zero (x : generatedAxisGlobalBinaryOrbit) :
    x.val ≠ 0 := by
  obtain ⟨c, hc⟩ := x.property
  intro hz
  have he : co1BinaryAction c (toAdd (qQuotHom sourceOmegaQ)) = co1BinaryAction c 0 := by
    exact hc.trans (hz.trans (map_zero _).symm)
  have h := congrFun ((co1BinaryAction c).injective he) (11 : Fin 24)
  simp [sourceOmegaQ_eq_frame_class, leechFrame_zero_hyperbolic] at h

/-- Every genuine Ω orbit point is singular for the actual extraspecial quadratic form. -/
theorem generatedAxisGlobalBinary_squareQuad (x : generatedAxisGlobalBinaryOrbit) :
    squareQuad x.val = 0 := by
  obtain ⟨c, hc⟩ := x.property
  change co1BinaryAction c (toAdd (qQuotHom sourceOmegaQ)) = x.val at hc
  rw [← hc, co1BinaryAction_squareQuad_invariant]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
