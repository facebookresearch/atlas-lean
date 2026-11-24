/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.Matching.StableMechanism

/-! # Tests for stable matching mechanisms and Roth's impossibility theorem -/

namespace MathlibExtTest.GameTheory.Matching.StableMechanism

open MathlibExt.Combinatorics.Matching.GaleShapley
open MathlibExt.GameTheory.Matching.StableMechanism

/-- Roth's two stable matchings are stable and distinct. -/
example : IsStable rothMenPrefs rothWomenPrefs rothX :=
  (roth_isStable_iff _).2 (Or.inl rfl)

example : IsStable rothMenPrefs rothWomenPrefs rothY :=
  (roth_isStable_iff _).2 (Or.inr rfl)

example : rothX ≠ rothY := fun h => absurd (congrArg (· 0) h) (by decide)

/-- The men prefer `x` and the women prefer `y`, with `m₂` and `w₃` indifferent. -/
example : (rothMenPrefs 0).lt (rothX 0) (rothY 0) ∧ (rothMenPrefs 2).lt (rothX 2) (rothY 2) ∧
    rothX 1 = rothY 1 := by decide

example : (rothWomenPrefs 0).lt (rothY.symm 0) (rothX.symm 0) ∧
    (rothWomenPrefs 1).lt (rothY.symm 1) (rothX.symm 1) := by decide

/-- The hypothesis of Roth's theorem is satisfiable: stable mechanisms exist (Gale–Shapley). -/
example : ∃ h : MatchingMechanism (Fin 3) (Fin 3), IsStableMechanism h :=
  ⟨fun mp wp => (gale_shapley_exists_stable_matching rfl mp wp).choose,
    fun mp wp => (gale_shapley_exists_stable_matching rfl mp wp).choose_spec⟩

/-- Stability is what drives the impossibility: a constant mechanism is strategy-proof. -/
example : IsStrategyProof (fun _ _ => Equiv.refl (Fin 3) : MatchingMechanism (Fin 3) (Fin 3)) :=
  ⟨fun m mp _ _ h => (mp m).irrefl _ h, fun w _ wp _ h => (wp w).irrefl _ h⟩

/-- Every stable mechanism is manipulated at Roth's profile, by `m₁` or by `w₁`. -/
example (h : MatchingMechanism (Fin 3) (Fin 3)) (hh : IsStableMechanism h) :
    ¬ IsStrategyProof h := fun hsp => not_exists_stable_strategyProof ⟨h, hh, hsp⟩

/-- The man-optimal stable matching of Roth's market is `x`. -/
example : IsManOptimalStable rothMenPrefs rothWomenPrefs rothX := by
  obtain ⟨μ, hμ⟩ := exists_isManOptimalStable rfl rothMenPrefs rothWomenPrefs
  rcases (roth_isStable_iff μ).1 hμ.1 with rfl | rfl
  · exact hμ
  · exact absurd (hμ.2 rothX ((roth_isStable_iff _).2 (Or.inl rfl)) 0) (by decide)

/-- A mechanism returning man-optimal stable matchings exists on every market with sides of
equal size, so the wanted Theorem 5 has satisfiable hypotheses. -/
example (n : ℕ) : ∃ h : MatchingMechanism (Fin n) (Fin n),
    ∀ mp wp, IsManOptimalStable mp wp (h mp wp) :=
  ⟨fun mp wp => (exists_isManOptimalStable rfl mp wp).choose,
    fun mp wp => (exists_isManOptimalStable rfl mp wp).choose_spec⟩

#print axioms exists_isManOptimalStable
#print axioms not_exists_stable_strategyProof
#print axioms roth_stable_mechanism_manipulable
#print axioms roth_isStable_iff

end MathlibExtTest.GameTheory.Matching.StableMechanism
