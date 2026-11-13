/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Hall subgroups of centralizers of automorphisms of prime order (Kourovka Notebook Problem 3.61)

Kourovka Notebook, Archive of Solved Problems, Problem 3.61 (L. A. Shemetkov): let `σ` be an
automorphism of prime order `p` of a finite group `G`, which has a Hall `π`-subgroup with cyclic
Sylow subgroups. Suppose that `p ∈ π`. Does the centralizer `C_G(σ)` have at least one Hall
`π`-subgroup?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Sylow
public import WantedExt.GroupTheory.DPiHallIntersectionKourovka18Problem31Wanted

@[expose] public section

namespace MathlibExt.GroupTheory.HallSubgroupAutomorphismCentralizerKourovka3Problem61Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 3.61 (L. A.
Shemetkov). UnsolvedMath record UM-00700209 (`KOU-3.61`), dataset ulamai/UnsolvedMath v1.8.0.

Hall `π`-subgroups are the `IsHallPiSubgroup` of the Kourovka 18.31 entry (order a `π`-number, index
with no prime divisor in `π`), reused here. `C_G(σ)` is the fixed-point subgroup `{g | σ g = g}`
(`MonoidHom.eqLocus`), and its Hall `π`-subgroups are taken inside it. "Cyclic Sylow subgroups"
means every Sylow `q`-subgroup, `q` prime, of the given Hall subgroup is cyclic. The answer depends
on the classification of finite simple groups (mod CFSG).
-/

open MathlibExt.GroupTheory.DPiHallIntersectionKourovka18Problem31Wanted

/-- Kourovka 3.61 (L. A. Shemetkov): let `σ` be an automorphism of prime order `p` of a finite
group `G` that has a Hall `π`-subgroup with cyclic Sylow subgroups, where `p ∈ π`. Then the
centralizer `C_G(σ) = {g | σ g = g}` has a Hall `π`-subgroup. -/
def automorphismCentralizerHasHallSubgroup : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (π : Set ℕ) (p : ℕ) (σ : MulAut G), p.Prime → p ∈ π →
    orderOf σ = p →
    (∃ H : Subgroup G, IsHallPiSubgroup π H ∧ ∀ q : ℕ, q.Prime → ∀ Q : Sylow q H, IsCyclic Q) →
    ∃ K : Subgroup ((σ : G →* G).eqLocus (MonoidHom.id G)), IsHallPiSubgroup π K

/--
Resolved true, modulo the classification of finite simple groups: the Kourovka Archive answers 3.61
"Yes, it does, mod CFSG", citing Mazurov, whose paper answers Shemetkov's question on normalizers of
soluble `π`-subgroups in a normal subgroup with a Hall `π`-subgroup with cyclic Sylow subgroups; if
a finite group `G` has a Hall `π`-subgroup with cyclic Sylow subgroups and `σ` is an automorphism of
`G` of prime order `p ∈ π`, then `C_G(σ)` has a Hall `π`-subgroup. Source: E. I. Khukhro and V. D.
Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 3.61 (L. A. Shemetkov); resolution:
V. D. Mazurov, A question of L. A. Shemetkov, Algebra and Logic 31 (1992), no. 6, 360-366, main
result (N. T. Vorob'ev's zbMATH review, Zbl 0819.20021: modulo CFSG, if a normal subgroup `K` of a
finite group has a Hall `π`-subgroup with cyclic Sylow subgroups and the quotient is a `D_π`-group,
then `N_K(M)` has a Hall `π`-subgroup for every soluble `π`-subgroup `M`); Kourovka Archive of
Solved Problems, Problem 3.61: Yes, it does, mod CFSG, https://doi.org/10.1007/BF02261729.
-/
public theorem_wanted automorphismCentralizerHasHallSubgroup_holds :
    automorphismCentralizerHasHallSubgroup

end MathlibExt.GroupTheory.HallSubgroupAutomorphismCentralizerKourovka3Problem61Wanted
