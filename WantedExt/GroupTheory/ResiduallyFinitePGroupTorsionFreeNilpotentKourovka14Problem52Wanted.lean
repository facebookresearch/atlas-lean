/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Residually finite `p`-groups and torsion-free nilpotence (Kourovka Notebook Problem 14.52)

Kourovka Notebook, Archive of Solved Problems, Problem 14.52 (Yu. V. Kuz'min): a finitely generated
residually torsion-free nilpotent group is residually a finite `p`-group for every prime `p`. Is the
converse true?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.Nilpotent

@[expose] public section

namespace MathlibExt.GroupTheory.ResiduallyFinitePGroupTorsionFreeNilpotentKourovka14Problem52Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 14.52 (Yu. V.
Kuz'min). UnsolvedMath record UM-00701037 (`KOU-14.52`), dataset ulamai/UnsolvedMath v1.8.0.

Residually `𝒫`: every `g ≠ 1` lies outside some normal subgroup `N` with `G / N ∈ 𝒫`. The converse
is stated for finitely generated groups, as in the problem.
-/

/-- Kourovka 14.52 (Yu. V. Kuz'min): every finitely generated group that is residually a finite
`p`-group for every prime `p` is residually torsion-free nilpotent. -/
def residuallyFinitePImpliesResiduallyTorsionFreeNilpotent : Prop :=
  ∀ (G : Type) [Group G], Group.FG G →
    (∀ p : ℕ, p.Prime → ∀ g : G, g ≠ 1 → ∃ (N : Subgroup G) (_ : N.Normal), g ∉ N ∧
      Finite (G ⧸ N) ∧ IsPGroup p (G ⧸ N)) →
    ∀ g : G, g ≠ 1 → ∃ (N : Subgroup G) (_ : N.Normal), g ∉ N ∧ Group.IsNilpotent (G ⧸ N) ∧
      ∀ y : G ⧸ N, y ≠ 1 → ¬ IsOfFinOrder y

/--
Resolved false: the Kourovka Archive answers 14.52 "Not always", citing Hartley: some finitely
generated group is residually a finite `p`-group for every prime `p` but is not residually
torsion-free nilpotent. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group
Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems,
Problem 14.52 (Yu. V. Kuz'min); resolution: B. Hartley, in: Symposia Mathematica XVII (Convegno sui
Gruppi Infiniti, INDAM, Roma, 1973), Academic Press, London, 1976, 225-234, Kourovka Archive,
Problem 14.52 (answer: Not always).
-/
public theorem_wanted residuallyFinitePImpliesResiduallyTorsionFreeNilpotent_refuted :
    ¬ residuallyFinitePImpliesResiduallyTorsionFreeNilpotent

end MathlibExt.GroupTheory.ResiduallyFinitePGroupTorsionFreeNilpotentKourovka14Problem52Wanted
