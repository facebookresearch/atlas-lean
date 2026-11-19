/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Isolated elements of odd prime order (Kourovka Notebook Problem 4.21)

Kourovka Notebook, Archive of Solved Problems, Problem 4.21 (G. Glauberman): let `G` be a finite
group, `p` an odd prime number, and `P` a Sylow `p`-subgroup of `G`. Let the order of every
non-identity normal subgroup of `G` be divisible by `p`. Suppose `P` has an element `x` that is
conjugate to no other from `P`. Does `x` belong to the centre of `G`? For `p = 2`, the answer is
positive (G. Glauberman, J. Algebra 4 (1966), 403-420).
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Sylow

@[expose] public section

namespace MathlibExt.GroupTheory.OddIsolatedElementCentralKourovka4Problem21Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 4.21 (G.
Glauberman). UnsolvedMath record UM-00700231 (`KOU-4.21`), dataset ulamai/UnsolvedMath v1.8.0.

"Conjugate to no other element of `P`" means that `gxg⁻¹ ∈ P` implies `gxg⁻¹ = x`. The target is
stated for elements `x` of order `p`, the case treated by Artemovich's paper (Isolated elements of
prime order in finite groups), which the Archive cites; isolated elements of higher order `p^k` are
not covered. The answer uses the classification of finite simple groups (mod CFSG).
-/

/-- Kourovka 4.21 (G. Glauberman), for elements of prime order: let `G` be a finite group, `p` an
odd prime, `P` a Sylow `p`-subgroup of `G`, and suppose every non-identity normal subgroup of `G`
has order divisible by `p`. If `x ∈ P` has order `p` and is conjugate in `G` to no element of `P`
other than itself, then `x` lies in the centre of `G`. -/
def oddIsolatedElementOfOrderPCentral : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (x : G), p.Prime → p ≠ 2 →
    (∀ N : Subgroup G, N.Normal → N ≠ ⊥ → p ∣ Nat.card N) → x ∈ P → orderOf x = p →
    (∀ g : G, g * x * g⁻¹ ∈ P → g * x * g⁻¹ = x) → x ∈ Subgroup.center G

/--
Resolved true, modulo the classification of finite simple groups, for elements of order `p`:
Artemovich proves that in a finite group `G` without non-trivial normal `p'`-subgroups, `p` odd, an
element of order `p` of a Sylow `p`-subgroup `P` that is conjugate to no other element of `P` is
central; the Kourovka Archive answers 4.21 "Yes, it does, mod CFSG". Source: E. I. Khukhro and V. D.
Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 4.21 (G. Glauberman); resolution: O.
D. Artemovich, Isolated elements of prime order in finite groups, Ukrain. Math. J. 40 (1988),
343-345, main theorem (S. A. Syskin's zbMATH review, Zbl 0662.20016: if all chief factors of the
finite group `G` are known simple groups and `O_{p'}(G) = 1`, an isolated element of prime order `p
> 2` lies in the centre of `G`); Kourovka Archive of Solved Problems, Problem 4.21: Yes, it does,
mod CFSG, https://doi.org/10.1007/BF01061317.
-/
public theorem_wanted oddIsolatedElementOfOrderPCentral_holds : oddIsolatedElementOfOrderPCentral

end MathlibExt.GroupTheory.OddIsolatedElementCentralKourovka4Problem21Wanted
