/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOddEigenRecognition
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisTransitionPairCoverage

/-! Actual compatible spin lifts of monomial lattice maps permute the
extraspecial orbit of the distinguished Hadamard state. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual pair-short eigenvalue of the distinguished state. -/
def generatedOddPairEigenSign (s : Fin 2) : ZMod 2 := if s = 0 then 0 else 1

/-- The implemented preferred pair operators have their original signed eigenvalues. -/
theorem generatedOddSpin_pair_eigen (s : Fin 2) (p : Fin 276) :
    spinRepresentation (griessShortQ (Sum.inl (s, p))) (generatedOddSpinState 0 1 0) =
      qSign (generatedOddPairEigenSign s) • generatedOddSpinState 0 1 0 := by
  change spinOperator _ _ = _
  fin_cases s
  · simpa [generatedOddPairEigenSign] using generatedOddSpin_pair_minus_eigen p
  · simpa [generatedOddPairEigenSign] using generatedOddSpin_pair_plus_eigen p

/-- A compatible lift transports an actual short eigenvector with its constructed central phase. -/
theorem generatedOddSpin_lift_eigen (f : localFiberSubgroup) (r : GriessShortIndex)
    (b : ZMod 2)
    (hr : spinRepresentation (griessShortQ r) (generatedOddSpinState 0 1 0) =
      qSign b • generatedOddSpinState 0 1 0) :
    spinRepresentation (griessShortQ (griessShortPermutation f.val.2 r))
      (f.val.1.val (generatedOddSpinState 0 1 0)) =
        qSign (localShortPhase f r + b) • f.val.1.val (generatedOddSpinState 0 1 0) := by
  have h := congrArg
    (fun e : SpinSpace ≃ₗ[ℝ] SpinSpace => e (f.val.1.val (generatedOddSpinState 0 1 0)))
    (spinConjugation_representation f.val.1 (griessShortQ r))
  rw [griessShortQ_image, map_mul, LinearEquiv.mul_apply, spinRepresentation_central] at h
  change qSign (localShortPhase f r) •
      spinRepresentation (griessShortQ (griessShortPermutation f.val.2 r))
        (f.val.1.val (generatedOddSpinState 0 1 0)) =
    f.val.1.val (spinRepresentation (griessShortQ r)
      (f.val.1.val.symm (f.val.1.val (generatedOddSpinState 0 1 0)))) at h
  rw [LinearEquiv.symm_apply_apply, hr, map_smul] at h
  have hh := congrArg (fun x : SpinSpace => qSign (localShortPhase f r) • x) h
  simpa only [smul_smul, qSign_sq, one_smul, ← qSign_add] using hh

/-- The actual monomial spin image is a signed common eigenvector of every pair operator. -/
theorem generatedOddSpin_monomial_pair_eigen (f : localFiberSubgroup)
    (hf : f.val.2 ∈ golayMonomialSubgroup) (s : Fin 2) (p : Fin 276) :
    ∃ b : ZMod 2, spinRepresentation (griessShortQ (Sum.inl (s, p)))
      (f.val.1.val (generatedOddSpinState 0 1 0)) =
        qSign b • f.val.1.val (generatedOddSpinState 0 1 0) := by
  obtain ⟨t, q, ht⟩ := generatedAxis_monomial_preserves_pair f.val.2⁻¹
    (golayMonomialSubgroup.inv_mem hf) s p
  have hp : griessShortPermutation f.val.2 (Sum.inl (t, q)) = Sum.inl (s, p) := by
    rw [map_inv] at ht
    change (griessShortPermutation f.val.2).symm (Sum.inl (s, p)) = Sum.inl (t, q) at ht
    have h := congrArg (fun r => griessShortPermutation f.val.2 r) ht
    simpa only [Equiv.apply_symm_apply] using h.symm
  refine ⟨localShortPhase f (Sum.inl (t, q)) + generatedOddPairEigenSign t, ?_⟩
  have h := generatedOddSpin_lift_eigen f (Sum.inl (t, q))
    (generatedOddPairEigenSign t) (generatedOddSpin_pair_eigen t q)
  rw [hp] at h
  exact h

/-- Every compatible monomial spin lift sends the distinguished state into its actual Q orbit. -/
theorem generatedOddSpin_monomial_Q_orbit (f : localFiberSubgroup)
    (hf : f.val.2 ∈ golayMonomialSubgroup) :
    ∃ q : Q, spinRepresentation q (generatedOddSpinState 0 1 0) =
      f.val.1.val (generatedOddSpinState 0 1 0) := by
  apply generatedOddSpin_common_eigen_Q_orbit
  · rw [f.val.1.property.2]
    exact generatedOddSpinState_pairing 0 1
  · intro p
    obtain ⟨b, hb⟩ := generatedOddSpin_monomial_pair_eigen f hf 0 p
    exact ⟨b, hb⟩
  · obtain ⟨b, hb⟩ := generatedOddSpin_monomial_pair_eigen f hf 1 0
    exact ⟨b, hb⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
