/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Covering systems with monochromatic moduli (Erdős Problem 8)

Erdős Problem 8 (Erdős and Graham): for any finite coloring of the integers, is there a covering
system all of whose moduli are monochromatic?
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.CoveringSystem

@[expose] public section

namespace MathlibExt.NumberTheory.MonochromaticCoveringSystemErdosProblem8Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #8, https://www.erdosproblems.com/8 (status DISPROVED
(LEAN)). UnsolvedMath record UM-30006678 (`EP-8`), dataset ulamai/UnsolvedMath v1.8.0.

A covering system is a finite set of residue classes `a mod m` covering `ℤ` (`MathlibExt`'s
`Int.IsCoveringSystem`, classes as pairs `(a, m)`), here with distinct moduli `m ≥ 2` (Erdős's
convention; the modulus `1` would make the question trivial). Only the colors of the moduli matter,
so the coloring is a function on `ℕ`. `WantedExt.NumberTheory.LargeModulusCoveringSystemsWanted`
states the underlying minimum modulus result (Erdős Problem 2), not this question.
formal-conjectures has no statement of this problem.
-/

/-- Erdős Problem 8 (Erdős and Graham): for every coloring of the positive integers with finitely
many colors there is a covering system with distinct moduli `m ≥ 2` (`Int.IsCoveringSystem`, the
classes being pairs `(a, m)` for `a mod m`) all of whose moduli have the same color. -/
def monochromaticCoveringSystem : Prop :=
  ∀ (k : ℕ) (col : ℕ → Fin k), ∃ (classes : Finset (ℤ × ℕ)) (i : Fin k),
    Int.IsCoveringSystem classes ∧ (∀ c ∈ classes, 2 ≤ c.2 ∧ col c.2 = i) ∧
      ∀ c ∈ classes, ∀ d ∈ classes, c.2 = d.2 → c = d

/--
Resolved false: Hough proved that every covering system with distinct moduli has a modulus below an
absolute bound (`10^18` on erdosproblems.com/8), so coloring each integer below the bound with its
own color and all larger integers with one new color admits no monochromatic covering system;
erdosproblems.com/8 lists the problem as disproved. Source: T. F. Bloom, Erdős Problems, Problem #8,
https://www.erdosproblems.com/8 (status DISPROVED (LEAN)); resolution: B. Hough, Solution of the
minimum modulus problem for covering systems, Ann. of Math. (2) 181 (2015), 361-382,
arXiv:1307.0874, arXiv abstract: the least modulus of a distinct covering system of congruences is
at most 10^18; erdosproblems.com/8: the answer to the coloring question is no, coloring all integers
below 10^18 with distinct colors and all other integers with one new color,
https://arxiv.org/abs/1307.0874.
-/
public theorem_wanted monochromaticCoveringSystem_refuted : ¬ monochromaticCoveringSystem

end MathlibExt.NumberTheory.MonochromaticCoveringSystemErdosProblem8Wanted
