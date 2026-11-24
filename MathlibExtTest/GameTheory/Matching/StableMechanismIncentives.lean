/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.Matching.StableMechanismIncentives

/-! # Tests for weak Pareto optimality in stable matching markets -/

namespace MathlibExtTest.GameTheory.Matching.StableMechanismIncentives

open MathlibExt.Combinatorics.Matching.GaleShapley
open MathlibExt.GameTheory.Matching.StableMechanism
open MathlibExt.GameTheory.Matching.StableMechanismIncentivesWanted

-- In the empty market, even a man-optimal matching vacuously improves on itself.
example (mp : MPrefs (Fin 0) (Fin 0)) (wp : WPrefs (Fin 0) (Fin 0)) :
    let μ := Equiv.refl (Fin 0)
    IsManOptimalStable mp wp μ ∧ ∀ m, (mp m).lt (μ m) (μ m) :=
  ⟨⟨fun m => m.elim0, fun _ _ m => m.elim0⟩, fun m => m.elim0⟩

-- In this profile, the identity is the unique stable matching. Exchanging the first
-- two partners improves both men, leaving the third indifferent.
private def womenRank : Fin 3 → Fin 3 → ℕ := ![rank3 0 2, rank3 1 2, rank3 2 0]

private def womenPrefs : WPrefs (Fin 3) (Fin 3) :=
  fun w => rankOrder (womenRank w) (by revert w; decide)

private theorem identity_optimal :
    IsManOptimalStable rothMenPrefs womenPrefs (Equiv.refl (Fin 3)) := by
  obtain ⟨μ, hμ⟩ := exists_isManOptimalStable rfl rothMenPrefs womenPrefs
  have unique : ∀ f : Fin 3 → Fin 3, Function.Injective f →
      StableByRanks rothMenRank womenRank f → ∀ i, f i = i := by decide
  have heq : μ = Equiv.refl (Fin 3) :=
    Equiv.ext (unique μ μ.injective ((isStable_iff_forall_partner _ _ μ).mp hμ.1))
  exact heq ▸ hμ

example :
    let ν := Equiv.swap (0 : Fin 3) 1
    (∀ m, m ≠ 2 → (rothMenPrefs m).lt (ν m) m) ∧ ν 2 = 2 ∧
      ¬ ∀ m, (rothMenPrefs m).lt (ν m) m :=
  ⟨by decide, by decide, not_forall_lt_of_isManOptimalStable _ _ identity_optimal _⟩

end MathlibExtTest.GameTheory.Matching.StableMechanismIncentives
