/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthBindE29p
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthBindE29m
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthBindS7c9p
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthBindR86p
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthBindR86n
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthBindE17p
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE17m
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhCells

/-! # Both triality images of the Twelfth root vectors 5, 33, 34, 35

Each statement is assembled from gated identification theorems of other workers (no coverage
hypothesis); in each case one vertex is bound directly by the target-side phase lemma and the
other one is the partner vertex of an explicitly bound image of the partner source vector:

* root 5: gident's `e29p_ident` (5+); partner of 5- = inverse image of the Eighth source vector,
  bound by `e29m_ident` (same source word `e29H`);
* root 33: gforest's `s7c9p_ident` (33-); partner of 33+ = inverse image of the Seventh cell 9
  vector, bound from its positive image by the phase merge `seventhCell_phase_merge` at cell 9;
* root 34: r8f's `wR8fR86p_ident` (34-); partner of 34+ = inverse image of the Root8 source
  vector, bound by `wR8fR86n_ident` (same source word);
* root 35: gident's `e17p_ident` (35-); partner of 35+ = inverse image of the Eighth source
  vector, bound by `e17m_ident` (same source word `e17H`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveTwelfthIdent
open GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- Both images of the Twelfth root 5 vector. -/
theorem twelfthRoot5_bound : sExtra (twelfthRootX 5) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
    sExtra⁻¹ (twelfthRootX 5) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  ⟨twelfthRoot5_pos_E29p, tbE29p_partner.mp tbE29m_src_mem⟩

set_option maxRecDepth 100000 in
/-- The inverse image of the Seventh cell 9 vector, written as the source of `s7c9p_ident`. -/
theorem tbS7c9p_src_neg : sExtra⁻¹ (rhoLocal (identWordLocal s7c9pH)
    (generatedAxisGlobalTwelveRepresentative 6)) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  obtain ⟨k, hk⟩ := seventhCell_phase_merge 9 (by decide)
  have hy := seventhCell_pos_of_ident 9 10 _ s7c9p_cell
  have hz := generatedAxisGlobalTwelve_union_mem_of_local _ k hy hk
  rw [seventhCellWord_ident, show seventhCellIdent 9 = s7c9pH from rfl] at hz
  exact hz

/-- Both images of the Twelfth root 33 vector. -/
theorem twelfthRoot33_bound : sExtra (twelfthRootX 33) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
    sExtra⁻¹ (twelfthRootX 33) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  ⟨tbS7c9p_partner.mp tbS7c9p_src_neg, twelfthRoot33_neg_S7c9p⟩

/-- Both images of the Twelfth root 34 vector. -/
theorem twelfthRoot34_bound : sExtra (twelfthRootX 34) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
    sExtra⁻¹ (twelfthRootX 34) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  refine ⟨?_, twelfthRoot34_neg_R86p⟩
  have h := tbR86n_src_mem
  rw [show wR8fR86nH = wR8fR86pH from rfl] at h
  exact tbR86p_partner.mp h

/-- Both images of the Twelfth root 35 vector. -/
theorem twelfthRoot35_bound : sExtra (twelfthRootX 35) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
    sExtra⁻¹ (twelfthRootX 35) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  ⟨tbE17p_partner.mp (generatedAxisGlobalTwelve_mem_of_transport 9 _ e17m_ident),
    twelfthRoot35_neg_E17p⟩

end GeneratedAxisGlobalTwelveTwelfthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
