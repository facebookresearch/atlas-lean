/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Complements of normal subgroups with Sylow direct factors (Kourovka Notebook Problem 7.44)

Kourovka Notebook, Archive of Solved Problems, Problem 7.44 (V. I. Sergiyenko): does a normal
subgroup `H` in a finite group `G` possess a complement in `G` if each Sylow subgroup of `H` is a
direct factor in some Sylow subgroup of `G`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.Sylow

@[expose] public section

namespace MathlibExt.GroupTheory.SylowDirectFactorComplementKourovka7Problem44Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 7.44 (V. I.
Sergiyenko). UnsolvedMath record UM-00700440 (`KOU-7.44`), dataset ulamai/UnsolvedMath v1.8.0.

A Sylow `p`-subgroup `P` of `H` (viewed in `G`) is a direct factor of the Sylow `p`-subgroup `Q` of
`G` when `Q` is the internal direct product of `P` and a subgroup `K`: `P ⊓ K = 1`, `P ⊔ K = Q` and
`P`, `K` commute elementwise. A complement is a subgroup `K` with `H.IsComplement' K`.
-/

/-- Kourovka 7.44 (V. I. Sergiyenko): if `H` is a normal subgroup of a finite group `G` and every
Sylow subgroup `P` of `H` is a direct factor of some Sylow subgroup `Q` of `G` (`Q` is the internal
direct product of `P` and some `K`), then `H` has a complement in `G`. -/
def sylowDirectFactorsGiveComplement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H : Subgroup G), H.Normal →
    (∀ (p : ℕ) [Fact p.Prime] (P : Sylow p H), ∃ Q : Sylow p G, ∃ K : Subgroup G,
      (P : Subgroup H).map H.subtype ⊓ K = ⊥ ∧ (P : Subgroup H).map H.subtype ⊔ K = Q ∧
        ∀ x ∈ (P : Subgroup H).map H.subtype, ∀ y ∈ K, x * y = y * x) →
    ∃ K : Subgroup G, H.IsComplement' K

/--
Resolved true: the Kourovka Archive answers 7.44 "Yes, it does", modulo the classification of finite
simple groups, citing Xiao, On a problem of Sergienko (1993). Source: E. I. Khukhro and V. D.
Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 7.44 (V. I. Sergiyenko); resolution:
W. Xiao, On a problem of Sergienko, J. Pure Appl. Algebra 87 (1993), 97-98, Kourovka Archive,
Problem 7.44: Yes, it does, mod CFSG, https://doi.org/10.1016/0022-4049(93)90072-2.
-/
public theorem_wanted sylowDirectFactorsGiveComplement_holds : sylowDirectFactorsGiveComplement

end MathlibExt.GroupTheory.SylowDirectFactorComplementKourovka7Problem44Wanted
