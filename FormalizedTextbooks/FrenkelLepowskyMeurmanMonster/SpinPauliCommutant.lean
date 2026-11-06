/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The actual real Pauli commutant, with orthogonality imposed on arbitrary endomorphisms. -/
module
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Finiteness

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- An arbitrary real spin endomorphism commuting with all actual Q operators is scalar.
The diagonal-character and translation argument is the proved scalar commutant in Finiteness. -/
theorem spinPauli_commutant_scalar (S : Module.End ℝ SpinSpace)
    (hcomm : ∀ q : Q, S.comp (spinOperator q) = (spinOperator q).comp S) :
    ∃ c : ℝ, S = c • LinearMap.id := by
  obtain ⟨c, hc⟩ := spinRepresentation_commutant_linear_scalar S (fun q x => by
    exact congrArg (fun T : Module.End ℝ SpinSpace => T x) (hcomm q))
  refine ⟨c, ?_⟩
  exact LinearMap.ext hc

/-- Form preservation forces the actual commuting scalar to be one of the two real signs.
No normalizer membership or inverse for S is assumed. -/
theorem spinPauli_commutant_orthogonal_scalar (S : Module.End ℝ SpinSpace)
    (hcomm : ∀ q : Q, S.comp (spinOperator q) = (spinOperator q).comp S)
    (horth : ∀ a b : SpinSpace, spinPairing (S a) (S b) = spinPairing a b) :
    ∃ c : ℝ, (c = 1 ∨ c = -1) ∧ S = c • LinearMap.id := by
  obtain ⟨c, hc⟩ := spinPauli_commutant_scalar S hcomm
  refine ⟨c, ?_, hc⟩
  have h := horth (Pi.single (0 : SpinIndex) 1) (Pi.single 0 1)
  rw [hc] at h
  have hsq : c * c = 1 := by
    simpa [spinPairing, Pi.single_apply, mul_ite, ite_mul] using h
  exact mul_self_eq_one_iff.mp hsq

/-- The residual orthogonal spin kernel is exactly constrained to ±Id. -/
theorem spinPauli_commutant_orthogonal_sign (S : Module.End ℝ SpinSpace)
    (hcomm : ∀ q : Q, S.comp (spinOperator q) = (spinOperator q).comp S)
    (horth : ∀ a b : SpinSpace, spinPairing (S a) (S b) = spinPairing a b) :
    S = LinearMap.id ∨ S = -LinearMap.id := by
  obtain ⟨c, hc, hS⟩ := spinPauli_commutant_orthogonal_scalar S hcomm horth
  rcases hc with hc | hc
  · left
    simpa only [hc, one_smul] using hS
  · right
    rw [hS]
    apply LinearMap.ext
    intro x
    funext t
    change c * x t = -x t
    rw [hc]
    ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
