/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# `p`-soluble supplements of maximal subgroups of Sylow subgroups (Kourovka Notebook Problem 17.111)

Kourovka Notebook, Archive of Solved Problems, Problem 17.111 (A. N. Skiba): let `G` be a finite
group, and `p` a prime divisor of `|G|`. Suppose that every maximal subgroup of a Sylow `p`-subgroup
of `G` has a `p`-soluble supplement in `G`. Must `G` be `p`-soluble?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Sylow

@[expose] public section

namespace MathlibExt.GroupTheory.SylowMaximalPSolubleSupplementKourovka17Problem111Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 17.111 (A. N.
Skiba). UnsolvedMath record UM-00701412 (`KOU-17.111`), dataset ulamai/UnsolvedMath v1.8.0.

A finite group is `p`-soluble when it has a chain `1 = H₀ ≤ ⋯ ≤ Hₙ = G`, each term normal in the
next, whose factors are `p`-groups or `p'`-groups (factor orders are relative indices). A maximal
subgroup of the Sylow subgroup `P` is a proper subgroup `M < P` with no subgroup strictly between
them, and a supplement of `M` is a subgroup `K` with `MK = G`. The hypothesis is stated for a given
Sylow `p`-subgroup; by Sylow's theorem it does not depend on the choice.
-/

/-- A finite group is `p`-soluble: it has a chain of subgroups `1 = H₀ ≤ H₁ ≤ ⋯ ≤ Hₙ = G`, each
normal in the next, such that every factor `H_{i+1}/H_i` is a `p`-group or a `p'`-group; the order
of the factor is the relative index of `H_i` in `H_{i+1}`. -/
def IsPSoluble (p : ℕ) (G : Type*) [Group G] : Prop :=
  ∃ (n : ℕ) (H : Fin (n + 1) → Subgroup G), H 0 = ⊥ ∧ H (Fin.last n) = ⊤ ∧
    ∀ i : Fin n, H i.castSucc ≤ H i.succ ∧ ((H i.castSucc).subgroupOf (H i.succ)).Normal ∧
      ((∃ k : ℕ, (H i.castSucc).relIndex (H i.succ) = p ^ k) ∨
        Nat.Coprime ((H i.castSucc).relIndex (H i.succ)) p)

/-- Kourovka 17.111 (A. N. Skiba): let `G` be a finite group and `p` a prime dividing `|G|`. If
every maximal subgroup `M` of a Sylow `p`-subgroup `P` of `G` has a `p`-soluble supplement `K`
(`MK = G`), then `G` is `p`-soluble. -/
def sylowMaximalSupplementPSoluble : Prop :=
  ∀ (p : ℕ) (G : Type) [Group G] [Finite G], p.Prime → p ∣ Nat.card G → ∀ P : Sylow p G,
    (∀ M : Subgroup G, M < P → (∀ L : Subgroup G, M < L → L ≤ P → L = P) →
      ∃ K : Subgroup G, IsPSoluble p K ∧ ∀ g : G, ∃ m ∈ M, ∃ k ∈ K, m * k = g) →
    IsPSoluble p G

/--
Resolved true: the Kourovka Archive answers 17.111 "Yes, it must", citing Qian (2013): if `p`
divides `|G|` and every maximal subgroup of a Sylow `p`-subgroup of the finite group `G` has a
`p`-soluble supplement in `G`, then `G` is `p`-soluble. Source: E. I. Khukhro and V. D. Mazurov
(eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49
(2026), Archive of Solved Problems, Problem 17.111 (A. N. Skiba); resolution: GuoHua Qian, Science
China Math. 56 (2013), 1015-1018, Kourovka Archive, Problem 17.111 (Yes, it must).
-/
public theorem_wanted sylowMaximalSupplementPSoluble_holds : sylowMaximalSupplementPSoluble

end MathlibExt.GroupTheory.SylowMaximalPSolubleSupplementKourovka17Problem111Wanted
