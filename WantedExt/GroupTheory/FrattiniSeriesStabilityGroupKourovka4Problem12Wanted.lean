/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Automorphisms stabilizing a series down to the Frattini subgroup (Kourovka Notebook Problem 4.12)

Kourovka Notebook, Archive of Solved Problems, Problem 4.12 (Ya. G. Berkovich): let `G` be a finite
group and `A` a group of automorphisms of `G` stabilizing a series of subgroups beginning with `G`
and ending with its Frattini subgroup. Then is `A` nilpotent?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Frattini

@[expose] public section

namespace MathlibExt.GroupTheory.FrattiniSeriesStabilityGroupKourovka4Problem12Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 4.12 (Ya. G.
Berkovich). UnsolvedMath record UM-00700223 (`KOU-4.12`), dataset ulamai/UnsolvedMath v1.8.0.

The series is `G = G₀ ≥ G₁ ≥ ⋯ ≥ Gₙ = Φ(G)` (Mathlib's `frattini G`) with every term normal in `G`;
`A` stabilizes it when `g⁻¹ α(g) ∈ Gᵢ₊₁` for all `α ∈ A`, `i < n` and `g ∈ Gᵢ`, and `A` may act
arbitrarily on `Φ(G)`. Requiring normal terms is the narrowest reading of "series of subgroups";
series with merely subnormal or arbitrary terms are not covered.
-/

/-- Kourovka 4.12 (Ya. G. Berkovich): let `A` be a group of automorphisms of a finite group `G`
stabilizing a series `G = G₀ ≥ G₁ ≥ ⋯ ≥ Gₙ = Φ(G)` of normal subgroups ending with the Frattini
subgroup: every `α ∈ A` acts trivially on each factor, `g⁻¹ α(g) ∈ Gᵢ₊₁` for `g ∈ Gᵢ`. Then `A` is
nilpotent. -/
def frattiniSeriesStabilityGroupNilpotent : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup (MulAut G)) (n : ℕ) (S : ℕ → Subgroup G),
    S 0 = ⊤ → S n = frattini G → (∀ i, (S i).Normal) → (∀ i < n, S (i + 1) ≤ S i) →
    (∀ α ∈ A, ∀ i < n, ∀ g ∈ S i, g⁻¹ * α g ∈ S (i + 1)) → Group.IsNilpotent A

/--
Resolved true: Schmid proves that a group of automorphisms of a finite group stabilizing a series
from the group down to its Frattini subgroup is nilpotent; the Kourovka Archive answers 4.12 "Yes,
it is". Stated for series of normal subgroups. Source: E. I. Khukhro and V. D. Mazurov (eds.),
Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026),
Archive of Solved Problems, Problem 4.12 (Ya. G. Berkovich); resolution: P. Schmid, Nilpotente
Gruppen und Stabilitätsgruppen, Math. Ann. 202 (1973), 57-69, Kourovka Archive of Solved Problems,
Problem 4.12: Yes, it is, https://doi.org/10.1007/BF01351205.
-/
public theorem_wanted frattiniSeriesStabilityGroupNilpotent_holds :
    frattiniSeriesStabilityGroupNilpotent

end MathlibExt.GroupTheory.FrattiniSeriesStabilityGroupKourovka4Problem12Wanted
