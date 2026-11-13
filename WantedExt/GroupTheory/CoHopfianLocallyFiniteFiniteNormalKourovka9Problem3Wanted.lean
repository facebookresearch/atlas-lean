/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Locally finite groups without proper isomorphic subgroups (Kourovka Notebook Problem 9.3)

Kourovka Notebook, Archive of Solved Problems, Problem 9.3 (V. V. Belyaev): suppose that a countable
locally finite group `G` contains no proper subgroups isomorphic to `G` itself and suppose that all
Sylow subgroups of `G` are finite. Does `G` possess a non-trivial finite normal subgroup?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.PGroup
public import WantedExt.GroupTheory.LocallyFiniteSimpleFiniteRankKourovka1Problem23Wanted

@[expose] public section

namespace MathlibExt.GroupTheory.CoHopfianLocallyFiniteFiniteNormalKourovka9Problem3Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 9.3 (V. V.
Belyaev). UnsolvedMath record UM-00700538 (`KOU-9.3`), dataset ulamai/UnsolvedMath v1.8.0.

Locally finite is the 1.23 entry's `IsLocallyFinite`: every finite subset generates a finite
subgroup, i.e. every finitely generated subgroup is finite. The Sylow `p`-subgroups of a locally
finite group are its maximal `p`-subgroups, and every `p`-subgroup lies in one (Zorn), so "all Sylow
subgroups are finite" is stated as "every `p`-subgroup is finite" for every prime `p`. `G` is taken
non-trivial: the trivial group meets the hypotheses and has no non-trivial normal subgroup.
-/

open MathlibExt.GroupTheory.LocallyFiniteSimpleFiniteRankKourovka1Problem23Wanted

/-- Kourovka 9.3 (V. V. Belyaev): a non-trivial countable locally finite group `G` with no proper
subgroup isomorphic to `G` and all of whose Sylow subgroups are finite (equivalently, every
`p`-subgroup is finite, since every `p`-subgroup lies in a Sylow, i.e. maximal, `p`-subgroup) has a
non-trivial finite normal subgroup. -/
def coHopfianFiniteSylowFiniteNormal : Prop :=
  ∀ (G : Type) [Group G], Countable G → IsLocallyFinite G → Nontrivial G →
    (∀ H : Subgroup G, Nonempty (H ≃* G) → H = ⊤) →
    (∀ p : ℕ, p.Prime → ∀ P : Subgroup G, IsPGroup p P → Finite P) →
    ∃ N : Subgroup G, N.Normal ∧ Finite N ∧ N ≠ ⊥

/--
Resolved true: the Kourovka Archive answers 9.3 "Yes, it does", citing Bell's thesis on locally
finite groups with Černikov Sylow subgroups: a non-trivial countable locally finite group with no
proper subgroup isomorphic to itself and finite Sylow subgroups has a non-trivial finite normal
subgroup. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 9.3
(V. V. Belyaev); resolution: S. D. Bell, Locally finite groups with Černikov Sylow subgroups, Ph.D.
thesis, University of Manchester, 1994, Kourovka Archive of Solved Problems, Problem 9.3: Yes, it
does, https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted coHopfianFiniteSylowFiniteNormal_holds : coHopfianFiniteSylowFiniteNormal

end MathlibExt.GroupTheory.CoHopfianLocallyFiniteFiniteNormalKourovka9Problem3Wanted
