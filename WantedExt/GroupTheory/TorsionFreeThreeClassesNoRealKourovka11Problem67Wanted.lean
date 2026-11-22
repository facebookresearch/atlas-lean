/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Torsion-free three-class groups without real elements (Kourovka Notebook Problem 11.67)

Kourovka Notebook, Problem 11.67 (B. Neumann): does there exist a torsion-free group with exactly 3
classes of conjugate elements such that no non-trivial conjugacy class contains a pair of inverse
elements?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.OrderOfElement

@[expose] public section

namespace MathlibExt.GroupTheory.TorsionFreeThreeClassesNoRealKourovka11Problem67Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 11.67 (B. Neumann). UnsolvedMath record
UM-00700759 (`KOU-11.67`), dataset ulamai/UnsolvedMath v1.8.0.

"No non-trivial class contains a pair of inverse elements" is `¬ IsConj g g⁻¹` for every `g ≠ 1`.
Torsion-free and "exactly three classes" are as in Kourovka 11.42.
-/

/-- Kourovka 11.67 (B. Neumann): there is a torsion-free group with exactly three conjugacy classes
in which no nontrivial conjugacy class contains a pair of mutually inverse elements, i.e. no
`g ≠ 1` is conjugate to `g⁻¹`. -/
def torsionFreeThreeClassesNoInverseConj : Prop :=
  ∃ (G : Type) (_ : Group G), (∀ g : G, g ≠ 1 → ¬ IsOfFinOrder g) ∧
    Nat.card (ConjClasses G) = 3 ∧ ∀ g : G, g ≠ 1 → ¬ IsConj g g⁻¹

/--
Resolved true: Bagayoko constructs a linearly ordered group with exactly three conjugacy classes
(positive transseries under composition); an ordered group is torsion-free, and conjugation
preserves positivity, so no `g ≠ 1` is conjugate to `g⁻¹`. The Kourovka Notebook (21st issue) marks
11.67 solved, "Yes, there does". Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems
in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 11.67 (B.
Neumann); resolution: V. Bagayoko, Ordered groups of formal series, and a conjugacy problem,
arXiv:2509.09186 (2025), main result: a linearly ordered group `(𝕋^{>ℝ}, ∘, <)` of transseries under
composition with exactly three conjugacy classes; the Kourovka Notebook (21st issue) marks 11.67
solved, https://arxiv.org/abs/2509.09186.
-/
public theorem_wanted torsionFreeThreeClassesNoInverseConj_holds :
    torsionFreeThreeClassesNoInverseConj

end MathlibExt.GroupTheory.TorsionFreeThreeClassesNoRealKourovka11Problem67Wanted
