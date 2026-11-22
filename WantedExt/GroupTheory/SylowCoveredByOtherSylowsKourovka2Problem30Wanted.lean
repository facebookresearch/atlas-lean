/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# A Sylow subgroup covered by the other Sylow subgroups (Kourovka Notebook Problem 2.30)

Kourovka Notebook, Archive of Solved Problems, Problem 2.30 (P. G. Kontorovich, A. L. Starostin):
does there exist a finite group in which a Sylow `p`-subgroup is covered by other Sylow
`p`-subgroups?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Sylow

@[expose] public section

namespace MathlibExt.GroupTheory.SylowCoveredByOtherSylowsKourovka2Problem30Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 2.30 (P. G.
Kontorovich, A. L. Starostin). UnsolvedMath record UM-00700105 (`KOU-2.30`), dataset
ulamai/UnsolvedMath v1.8.0.

Stated for every prime `p`, as answered. "Covered" means the Sylow subgroup is contained in the
union of the other Sylow `p`-subgroups (Mathlib's `Sylow p G`).
-/

/-- Kourovka 2.30 (P. G. Kontorovich, A. L. Starostin), in the form answered: for every prime `p`
there is a finite group with a Sylow `p`-subgroup `P` covered by the other Sylow `p`-subgroups. -/
def sylowCoveredByOtherSylows : Prop :=
  ∀ p : ℕ, p.Prime → ∃ (G : Type) (_ : Group G) (_ : Finite G) (P : Sylow p G),
    (P : Set G) ⊆ ⋃ (Q : Sylow p G) (_ : Q ≠ P), (Q : Set G)

/--
Resolved true: the Kourovka Archive answers 2.30 "Yes, there does, for any prime `p`", citing
Mazurov. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 2.30
(P. G. Kontorovich, A. L. Starostin); resolution: V. D. Mazurov, Ural. Gos. Univ. Mat. Zap. 7, no. 3
(1969/70), 129-132 (Russian), Kourovka Archive, Problem 2.30: Yes, there does, for any prime p,
https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted sylowCoveredByOtherSylows_holds : sylowCoveredByOtherSylows

end MathlibExt.GroupTheory.SylowCoveredByOtherSylowsKourovka2Problem30Wanted
