/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact fingerprints of actual original-source inverse root-set transports. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3TCMembershipValidation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3TCRepresentativeSource

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Pointwise

/-- The actual original-source inverse root transport has its checked integer fingerprint. -/
theorem y322Orthogonal3TCMembership_source_value (i : Fin 3159) :
    y322Orthogonal3TCMembershipFingerprint
        ((y322Orthogonal3Hom (y322TCIndexRepresentative i))⁻¹ • y322Orthogonal3E7Roots) =
      y322Orthogonal3TCMembershipValue i := by
  rw [← y322Orthogonal3TCMembershipEval_exact, y322Orthogonal3TCRepresentative_matrix]
  exact y322Orthogonal3TCMembership_matrix_value i

/-- All 3159 actual source representatives give distinct inverse transports of the E7 root set. -/
theorem y322Orthogonal3TCRepresentative_roots_injective : Function.Injective
    (fun i : Fin 3159 =>
      (y322Orthogonal3Hom (y322TCIndexRepresentative i))⁻¹ • y322Orthogonal3E7Roots) := by
  intro i j hij
  apply y322Orthogonal3TCMembershipValue_injective
  rw [← y322Orthogonal3TCMembership_source_value, ← y322Orthogonal3TCMembership_source_value]
  exact congrArg y322Orthogonal3TCMembershipFingerprint hij

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
