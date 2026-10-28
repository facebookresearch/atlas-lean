/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthBindW1n
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthBindW21p
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthBindW9p
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthBindW13p
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthBindW30p
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthBindN3p
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthBindN3n
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthBindR3p
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthBindE11x

/-! # Both triality images of the Twelfth root vectors 1, 9, 13, 21, 23, 30, 31, 37

Each statement is assembled from gated identification theorems (no coverage hypothesis):

* roots 1, 13, 30: one pure Twelfth identification each (`twGtwelfthW1n_ident`,
  `twGtwelfthW13p_ident`, r8f's `wGtwelfthW30p_ident`), source and target vertices;
* roots 9, 21: `twGtwelfthW21p_ident` (21+, 9+) and `twGtwelfthW9p_ident` (9+, 21-); the image
  9- is the partner vertex of 21+ in the triangle of `twGtwelfthW9p_ident`;
* root 23: gident's `e11x_ident` (23-) and `e11p_ident` (the positive image of the common Eighth
  source vector, which is the partner vertex of 23+);
* root 31: gident2/gninth's `wGninthN3pX_ident` (31+) and `wGninthN3nX_ident` (the inverse image
  of the common Ninth source vector, which is the partner vertex of 31-);
* root 37: grecip's `fourthR3p_ident` (37+) and `fourth_root3_bound` (partner vertex of 37-). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveTwelfthIdent
open GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- Both images of the Twelfth root 1 vector. -/
theorem twelfthRoot1_bound : sExtra (twelfthRootX 1) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
    sExtra⁻¹ (twelfthRootX 1) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  ⟨twelfthRoot1_pos_W1n, twelfthRoot1_neg_W1n⟩

/-- Both images of the Twelfth root 9 vector. -/
theorem twelfthRoot9_bound : sExtra (twelfthRootX 9) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
    sExtra⁻¹ (twelfthRootX 9) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  ⟨twelfthRoot9_pos_W9p, tbW9p_partner.mpr twelfthRoot21_pos_W21p⟩

/-- Both images of the Twelfth root 13 vector. -/
theorem twelfthRoot13_bound : sExtra (twelfthRootX 13) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
    sExtra⁻¹ (twelfthRootX 13) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  ⟨twelfthRoot13_pos_W13p, twelfthRoot13_neg_W13p⟩

/-- Both images of the Twelfth root 21 vector. -/
theorem twelfthRoot21_bound : sExtra (twelfthRootX 21) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
    sExtra⁻¹ (twelfthRootX 21) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  ⟨twelfthRoot21_pos_W21p, twelfthRoot21_neg_W9p⟩

/-- Both images of the Twelfth root 23 vector. -/
theorem twelfthRoot23_bound : sExtra (twelfthRootX 23) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
    sExtra⁻¹ (twelfthRootX 23) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  ⟨tbE11x_partner.mp (generatedAxisGlobalTwelve_mem_of_transport 7 _ e11p_ident),
    twelfthRoot23_neg_E11x⟩

/-- Both images of the Twelfth root 30 vector. -/
theorem twelfthRoot30_bound : sExtra (twelfthRootX 30) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
    sExtra⁻¹ (twelfthRootX 30) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  ⟨twelfthRoot30_pos_W30p, twelfthRoot30_neg_W30p⟩

/-- Both images of the Twelfth root 31 vector. -/
theorem twelfthRoot31_bound : sExtra (twelfthRootX 31) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
    sExtra⁻¹ (twelfthRootX 31) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  refine ⟨twelfthRoot31_pos_N3p, ?_⟩
  have h := tbN3n_src_mem
  rw [show wGninthN3nXH = wGninthN3pXH from rfl] at h
  exact tbN3p_partner.mp h

/-- Both images of the Twelfth root 37 vector. -/
theorem twelfthRoot37_bound : sExtra (twelfthRootX 37) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
    sExtra⁻¹ (twelfthRootX 37) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  ⟨twelfthRoot37_pos_R3p, twelfthRoot37_neg_R3p⟩

end GeneratedAxisGlobalTwelveTwelfthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
