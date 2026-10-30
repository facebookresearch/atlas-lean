/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Uncomplemented maximal subgroups of Sylow subgroups (Kourovka Notebook Problem 15.81)

Kourovka Notebook, Archive of Solved Problems, Problem 15.81 (A. N. Skiba): let `G` be a finite
non-supersoluble group. Is it true that `G` has a non-cyclic Sylow subgroup `P` such that some
maximal subgroup of `P` has no proper complement in `G`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Sylow

@[expose] public section

namespace MathlibExt.GroupTheory.NonSupersolubleUncomplementedMaximalKourovka15Problem81Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 15.81 (A. N.
Skiba). UnsolvedMath record UM-00701169 (`KOU-15.81`), dataset ulamai/UnsolvedMath v1.8.0.

Supersoluble means a series of normal subgroups of `G` from `1` to `G` with cyclic factors. A
complement of `M` is a subgroup `K` with `M K = G` (product of sets) and `M ∩ K = 1`; "proper" is
kept as `K ≠ G`, automatic when `M ≠ 1`. A maximal subgroup of `P` is a subgroup `M < P` with no
subgroup strictly between `M` and `P`.
-/

open scoped Pointwise

/-- `G` is supersoluble: it has a series `1 = H₀ ≤ ⋯ ≤ Hₙ = G` of normal subgroups of `G` with
cyclic factors. -/
def IsSupersoluble (G : Type*) [Group G] : Prop :=
  ∃ (n : ℕ) (H : Fin (n + 1) → Subgroup G), H 0 = ⊥ ∧ H (Fin.last n) = ⊤ ∧ (∀ i, (H i).Normal) ∧
    ∀ i : Fin n, H i.castSucc ≤ H i.succ ∧
      ∃ g ∈ H i.succ, ∀ x ∈ H i.succ, ∃ k : ℤ, x * (g ^ k)⁻¹ ∈ H i.castSucc

/-- Kourovka 15.81 (A. N. Skiba): every finite non-supersoluble group `G` has a non-cyclic Sylow
subgroup `P` with a maximal subgroup `M` that has no proper complement in `G`, i.e. no `K < G` with
`M K = G` and `M ∩ K = 1`. -/
def nonSupersolubleHasUncomplementedSylowMaximal : Prop :=
  ∀ (G : Type) [Group G] [Finite G], ¬ IsSupersoluble G →
    ∃ p : ℕ, p.Prime ∧ ∃ P : Sylow p G, ¬ IsCyclic (P : Subgroup G) ∧
      ∃ M : Subgroup G, M < P ∧ (∀ L : Subgroup G, M < L → L ≤ P → L = P) ∧
        ¬ ∃ K : Subgroup G, K ≠ ⊤ ∧ (M : Set G) * (K : Set G) = Set.univ ∧ M ⊓ K = ⊥

/--
Resolved true: the Kourovka Archive answers 15.81 "Yes, it is" (Wang and Wei): every finite
non-supersoluble group has a non-cyclic Sylow subgroup with a maximal subgroup that has no proper
complement. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 15.81
(A. N. Skiba); resolution: Wang Yanming and Wei Huaquan, Sci. China Ser. A 47 (2004), no. 1, 96-103,
Kourovka Archive, Problem 15.81 (answer: Yes, it is).
-/
public theorem_wanted nonSupersolubleHasUncomplementedSylowMaximal_holds :
    nonSupersolubleHasUncomplementedSylowMaximal

end MathlibExt.GroupTheory.NonSupersolubleUncomplementedMaximalKourovka15Problem81Wanted
