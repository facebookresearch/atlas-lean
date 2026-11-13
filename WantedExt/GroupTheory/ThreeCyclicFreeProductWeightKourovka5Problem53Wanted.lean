/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Free products of three cyclic groups of prime orders (Kourovka Notebook Problem 5.53)

Kourovka Notebook, Archive of Solved Problems, Problem 5.53 (J. Wiegold, after P. Scott): let p, q,
r be distinct prime numbers; prove that the free product G = C_p * C_q * C_r of cyclic groups of
orders p, q, r is not the normal closure of a single element.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.GroupTheory.PresentedGroup

@[expose] public section

namespace MathlibExt.GroupTheory.ThreeCyclicFreeProductWeightKourovka5Problem53Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 5.53 (J.
Wiegold, after P. Scott). UnsolvedMath record UM-00700334 (`KOU-5.53`), dataset ulamai/UnsolvedMath
v1.8.0.

`C_p * C_q * C_r` is the presented group `⟨a, b, c | a^p, b^q, c^r⟩`.
-/

/-- The free product `C_p * C_q * C_r = ⟨a, b, c | a^p, b^q, c^r⟩` of cyclic groups of orders `p`,
`q`, `r`. -/
abbrev threeCyclicFreeProduct (p q r : ℕ) : Type :=
  PresentedGroup ({FreeGroup.of 0 ^ p, FreeGroup.of 1 ^ q, FreeGroup.of 2 ^ r} :
    Set (FreeGroup (Fin 3)))

/-- Kourovka 5.53 (J. Wiegold, after P. Scott): for distinct primes `p`, `q`, `r`, the free product
`C_p * C_q * C_r` is not the normal closure of a single element. -/
def threeCyclicFreeProductNotNormallyMonogenic : Prop :=
  ∀ p q r : ℕ, p.Prime → q.Prime → r.Prime → p ≠ q → q ≠ r → p ≠ r →
    ∀ g : threeCyclicFreeProduct p q r, Subgroup.normalClosure {g} ≠ ⊤

/--
Resolved true: the Kourovka Archive records 5.53 as proved by Howie, A proof of the Scott-Wiegold
conjecture on free products of cyclic groups (J. Pure Appl. Algebra 173 (2002), 167-176). Source: E.
I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 5.53 (J. Wiegold, after P.
Scott); resolution: J. Howie, A proof of the Scott-Wiegold conjecture on free products of cyclic
groups, J. Pure Appl. Algebra 173 (2002), no. 2, 167-176, Kourovka Archive, Problem 5.53: This is
proved (Howie); the Scott-Wiegold conjecture of the title is the statement of Problem 5.53,
https://doi.org/10.1016/S0022-4049(02)00042-7.
-/
public theorem_wanted threeCyclicFreeProductNotNormallyMonogenic_holds :
    threeCyclicFreeProductNotNormallyMonogenic

end MathlibExt.GroupTheory.ThreeCyclicFreeProductWeightKourovka5Problem53Wanted
