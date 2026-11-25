/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Notation
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Tactic.ByContra

/-!
# Monochromatic progressions with large difference

We prove Erdős Problem 645 by comparing two progressions with the same endpoint. If the
colouring avoids all the required triples, both colours occur arbitrarily far out. Yet two
differently coloured points at distance two force one colour to persist from some point on.

Source: T. F. Bloom, Erdős Problems, Problem #645, https://www.erdosproblems.com/645 (status PROVED
(LEAN)). UnsolvedMath record UM-30006965 (`EP-645`), dataset ulamai/UnsolvedMath v1.8.0.

`ℕ` is the positive integers, so `x ≥ 1` (the colour of `0` plays no role); colourings are functions
to `Bool`. Compared with the formal-conjectures statement `ErdosProblems/645.lean` (equivalent; no
code imported).
-/

@[expose] public section

namespace MathlibExt.Combinatorics.MonochromaticProgressionLargeDifferenceErdosProblem645Wanted

/-- **Erdős Problem 645.** The statement that for every colouring of the positive integers with
two colours there are positive integers $x$ and $d$ with $d > x$ such that $x$, $x + d$ and
$x + 2d$ all have the same colour. -/
def monochromaticProgressionLargeDifference : Prop :=
  ∀ c : ℕ → Bool, ∃ x d : ℕ, 0 < x ∧ x < d ∧ c x = c (x + d) ∧ c (x + d) = c (x + 2 * d)

/--
**Erdős Problem 645 is true.** For every colouring of the positive integers with two colours
there are positive integers $x$ and $d$ with $d > x$ such that $x$, $x + d$ and $x + 2d$ all
have the same colour.

Brown and Landman proved more: for every increasing function $f$ there is such a monochromatic
progression with $d > f(x)$. Erdős Problems also records a short argument of Alweiss.

Source:
T. F. Bloom, Erdős Problems, Problem #645, https://www.erdosproblems.com/645 (status PROVED (LEAN));
resolution: T. C. Brown and B. M. Landman, Monochromatic arithmetic progressions with large
differences, Bull. Austral. Math. Soc. (1999), 21-35, erdosproblems.com/645: first proved by Brown
and Landman, with d > f(x) for any increasing f; the page records a short argument of Alweiss,
https://www.erdosproblems.com/645.
-/
public theorem monochromaticProgressionLargeDifference_holds :
    monochromaticProgressionLargeDifference := by
  intro c
  by_contra h
  -- The third point of a sufficiently widely spaced progression is forced.
  have endpoint {x y z : ℕ} (hx : 0 < x) (hy : 2 * x < y) (hz : x + z = 2 * y)
      (hxy : c x = c y) : c z = !c x := by
    apply Bool.eq_not_iff.mpr
    intro hzx
    apply h
    refine ⟨x, y - x, hx, by omega, ?_, ?_⟩
    · rwa [show x + (y - x) = y by omega]
    · rw [show x + (y - x) = y by omega, show x + 2 * (y - x) = z by omega, hzx, hxy]
  -- A tail missing one colour would contain a monochromatic triple x, 3x, 5x.
  have occurs (N : ℕ) (b : Bool) : ∃ m ≥ N, c m = b := by
    by_contra! hmiss
    have ht (m : ℕ) (hm : N ≤ m) : c m = !b := Bool.eq_not_iff.mpr (hmiss m hm)
    refine h ⟨N + 1, 2 * (N + 1), by omega, by omega, ?_, ?_⟩ <;>
      rw [ht _ (by omega), ht _ (by omega)]
  -- At least one adjacent pair in 1, 3, 5 changes colour.
  obtain ⟨a, ha, hdiff⟩ : ∃ a : ℕ, 0 < a ∧ c a ≠ c (a + 2) := by
    by_cases h₁ : c 1 = c 3
    · exact ⟨3, by decide, fun h₂ ↦ h ⟨1, 2, by decide, by decide, h₁, h₂⟩⟩
    · exact ⟨1, by decide, h₁⟩
  obtain ⟨m, hm, hcm⟩ := occurs (2 * a + 4) (c a)
  -- If n, n+1 repeat the colours of a, a+2, their common endpoint needs both colours.
  have step (n : ℕ) (hn : m ≤ n) (hc : c n = c a) : c (n + 1) = c a := by
    by_contra hnext
    have hpair : c (a + 2) = c (n + 1) :=
      (Bool.eq_not_iff.mpr hdiff.symm).trans (Bool.eq_not_iff.mpr hnext).symm
    let z := 2 * n - a
    have h₁ : c z = !c a := endpoint ha (by omega) (by dsimp [z]; omega) hc.symm
    have h₂ : c z = !c (a + 2) := endpoint (by omega) (by omega) (by dsimp [z]; omega) hpair
    exact hdiff (by simpa using congrArg Bool.not (h₁.symm.trans h₂))
  obtain ⟨k, hk, hck⟩ := occurs m (c (a + 2))
  have hconst : c k = c a := Nat.le_induction hcm step k hk
  exact hdiff (hconst.symm.trans hck)

end MathlibExt.Combinatorics.MonochromaticProgressionLargeDifferenceErdosProblem645Wanted
