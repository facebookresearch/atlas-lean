/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Matching.GaleShapleyMechanism

/-! # Tests for deferred acceptance as a matching mechanism -/

namespace Cslib.Algorithms.Lean.Matching.GaleShapley

open MathlibExt.GameTheory.Matching.StableMechanism

/-- On Roth's market every man-optimal stable mechanism, deferred acceptance included, returns
Roth's matching `x`. -/
example (h : MatchingMechanism (Fin 3) (Fin 3))
    (hh : ∀ mp wp, IsManOptimalStable mp wp (h mp wp)) :
    h rothMenPrefs rothWomenPrefs = rothX := by
  obtain ⟨hs, hopt⟩ := hh rothMenPrefs rothWomenPrefs
  rcases (roth_isStable_iff _).1 hs with e | e
  · exact e
  · exfalso
    have hx : MathlibExt.Combinatorics.Matching.GaleShapley.IsStable rothMenPrefs rothWomenPrefs
        rothX := (roth_isStable_iff _).2 (Or.inl rfl)
    have := hopt rothX hx 0
    rw [e] at this
    exact this (by decide)

/-- Such mechanisms exist: deferred acceptance on rankings. -/
example : ∃ h : MatchingMechanism (Fin 3) (Fin 3), ∀ mp wp, IsManOptimalStable mp wp (h mp wp) :=
  exists_isManOptimalStable_mechanism 3

#print axioms exists_isManOptimalStable_mechanism

end Cslib.Algorithms.Lean.Matching.GaleShapley
