/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsShortCoordinateCertificate

/-! Complete actual Q images transport entire finitely supported short constituents. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Every genuine Q-image certificate determines the whole actual short-unit image. -/
theorem generatedFeasibleContainingZeroSparseShort_basis
    (f : localFiberSubgroup) (r s : GriessShortIndex) (p : ZMod 2)
    (hq : spinConjugation f.val.1 (griessShortQ r) = qCentral p * griessShortQ s) :
    localShortOperator f (Pi.single r (1 : ℝ)) =
      qSign p • Pi.single s (1 : ℝ) := by
  apply monsterNortonShortBasis_of_Q_image
  rw [monsterNortonShortQ_eq, monsterNortonShortQ_eq]
  exact hq

/-- All support addresses and actual binary phases are retained in the entire short sum. -/
theorem generatedFeasibleContainingZeroSparseShort_sum {ι : Type*} [Fintype ι]
    (f : localFiberSubgroup) (r s : ι → GriessShortIndex)
    (p : ι → ZMod 2) (c : ι → ℝ)
    (hq : ∀ i, spinConjugation f.val.1 (griessShortQ (r i)) =
      qCentral (p i) * griessShortQ (s i)) :
    localShortOperator f (∑ i, c i • Pi.single (r i) (1 : ℝ)) =
      ∑ i, (c i * qSign (p i)) • Pi.single (s i) (1 : ℝ) := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, generatedFeasibleContainingZeroSparseShort_basis f _ _ _ (hq i),
    smul_smul]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
