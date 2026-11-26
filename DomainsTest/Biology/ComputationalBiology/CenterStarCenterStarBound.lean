/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.ComputationalBiology.CenterStarCenterStarBound
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Tests for the center-star bound -/

@[expose] public section

namespace DomainsTest.Biology.ComputationalBiology.CenterStarCenterStarBound

open WantedExt.Biology.ComputationalBiology.CenterStarWanted

example {α : Type*} [DecidableEq α] (s : Option α → Option α → ℝ)
    (hgap : s none none = 0)
    (hdiag : ∀ x : Option α, s x x = 0)
    (htria : ∀ x y z : Option α, s x z ≤ s x y + s y z)
    (hsymm : ∀ x y : Option α, s x y = s y x)
    (X : Fin 2 → List α)
    (hD_le : ∀ (U V : List α) (A : PairAlignment α),
      IsPairAlignmentOf A U V → pairDist s U V ≤ alignValue s A)
    (hD_att : ∀ U V : List α, ∃ A : PairAlignment α,
      IsPairAlignmentOf A U V ∧ pairDist s U V = alignValue s A)
    (c : Fin 2)
    (hcenter : ∀ i : Fin 2, centerTotal s X (X c) ≤ centerTotal s X (X i))
    (Ac : MSAlignment α 2)
    (hac : msErasesTo Ac X)
    (hproj : ∀ i, inducedValue s Ac c i = pairDist s (X c) (X i))
    (Astar : MSAlignment α 2)
    (hastar : msErasesTo Astar X)
    (hopt : ∀ A' : MSAlignment α 2, msErasesTo A' X →
      msaValue s Astar ≤ msaValue s A') :
    msaValue s Ac ≤ msaValue s Astar := by
  have h := centerStar_bound s hgap hdiag htria hsymm 2 (le_refl 2) X
    hD_le hD_att c hcenter Ac hac hproj Astar hastar hopt
  simp only [Nat.cast_ofNat] at h
  linarith

example {α : Type*} [DecidableEq α] (s : Option α → Option α → ℝ)
    (hgap : s none none = 0)
    (hdiag : ∀ x : Option α, s x x = 0)
    (htria : ∀ x y z : Option α, s x z ≤ s x y + s y z)
    (hsymm : ∀ x y : Option α, s x y = s y x)
    (k : ℕ) (hk : 2 ≤ k)
    (X : Fin k → List α)
    (hD_le : ∀ (U V : List α) (A : PairAlignment α),
      IsPairAlignmentOf A U V → pairDist s U V ≤ alignValue s A)
    (hD_att : ∀ U V : List α, ∃ A : PairAlignment α,
      IsPairAlignmentOf A U V ∧ pairDist s U V = alignValue s A)
    (c : Fin k)
    (hcenter : ∀ i : Fin k, centerTotal s X (X c) ≤ centerTotal s X (X i))
    (Ac : MSAlignment α k)
    (hac : msErasesTo Ac X)
    (hproj : ∀ i, inducedValue s Ac c i = pairDist s (X c) (X i))
    (Astar : MSAlignment α k)
    (hastar : msErasesTo Astar X)
    (hopt : ∀ A' : MSAlignment α k, msErasesTo A' X →
      msaValue s Astar ≤ msaValue s A')
    (hpos : 0 < msaValue s Astar) :
    msaValue s Ac / msaValue s Astar ≤ 2 * ((k : ℝ) - 1) / k := by
  have h := centerStar_bound s hgap hdiag htria hsymm k hk X
    hD_le hD_att c hcenter Ac hac hproj Astar hastar hopt
  have hk0 : (0 : ℝ) < (k : ℝ) := by
    have h1k : (1 : ℕ) ≤ k := le_trans (by decide) hk
    have hh : ((1 : ℕ) : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr h1k
    rw [Nat.cast_one] at hh
    linarith
  rw [div_le_iff₀ hpos]
  have hdiv : msaValue s Ac ≤
      (2 * ((k : ℝ) - 1) * msaValue s Astar) / k := by
    rw [le_div_iff₀ hk0]
    linarith [h]
  calc msaValue s Ac
      ≤ (2 * ((k : ℝ) - 1) * msaValue s Astar) / k := hdiv
    _ = (2 * ((k : ℝ) - 1) / k) * msaValue s Astar := by ring

end DomainsTest.Biology.ComputationalBiology.CenterStarCenterStarBound
