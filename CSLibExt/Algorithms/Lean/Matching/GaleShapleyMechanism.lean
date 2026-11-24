/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Matching.GaleShapley
public import MathlibExt.GameTheory.Matching.StableMechanism

/-!
# Deferred acceptance as a matching mechanism

The executable Gale–Shapley algorithm (`gsMatching`) computes, for every preference profile on
`Fin n`, the man-optimal stable matching. Read as a rule from stated profiles to matchings, it is
the mechanism of Roth's Theorem 5 (A. E. Roth, "The economics of matching: stability and
incentives", *Mathematics of Operations Research* 7(4) (1982), 617–628, Theorem 5 and its proof
in §5, which uses this "repeated proposal procedure"). In particular the hypothesis of the wanted
statement `isTruthfulDominantForMan_of_isManOptimalStable`
(`MathlibExt.GameTheory.Matching.StableMechanismIncentivesWanted`) is satisfiable.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.Matching.GaleShapley

open MathlibExt.Combinatorics.Matching.GaleShapley (MPrefs WPrefs)
open MathlibExt.GameTheory.Matching.StableMechanism

/-- **Deferred acceptance is a man-optimal stable mechanism** (Gale and Shapley, *Amer. Math.
Monthly* 69 (1962), Theorems 1 and 2; Roth, *Math. Oper. Res.* 7 (1982), Theorems 1, 2 and §5).
For every `n` there is a matching mechanism on `n` men and `n` women, namely deferred acceptance
run on rankings presenting the stated preferences, that returns the man-optimal stable matching
of every stated profile. -/
theorem exists_isManOptimalStable_mechanism (n : ℕ) :
    ∃ h : MatchingMechanism (Fin n) (Fin n), ∀ mp wp, IsManOptimalStable mp wp (h mp wp) := by
  choose σ τ _ _ hs hopt using fun (mp : MPrefs (Fin n) (Fin n)) (wp : WPrefs (Fin n) (Fin n)) =>
    exists_rankings_gsMatching mp wp
  exact ⟨fun mp wp => gsMatching (σ mp wp) (τ mp wp), fun mp wp => ⟨hs mp wp, hopt mp wp⟩⟩

end Cslib.Algorithms.Lean.Matching.GaleShapley
