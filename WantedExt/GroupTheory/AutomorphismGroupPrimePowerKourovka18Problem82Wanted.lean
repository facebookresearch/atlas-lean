/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Prime powers dividing the order of the automorphism group (Kourovka Notebook Problem 18.82)

Kourovka Notebook, Archive of Solved Problems, Problem 18.82 (R. M. Patne): is there a function `f :
ℕ → ℕ` such that for any prime `p`, if `p^{f(n)}` divides the order of a finite group `G`, then `pⁿ`
divides the order of `Aut G`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

namespace MathlibExt.GroupTheory.AutomorphismGroupPrimePowerKourovka18Problem82Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 18.82 (R. M.
Patne). UnsolvedMath record UM-00701511 (`KOU-18.82`), dataset ulamai/UnsolvedMath v1.8.0.

`Aut G` is `MulAut G`; `f` does not depend on `p`.
-/

/-- Kourovka 18.82 (R. M. Patne): there is a function `f : ℕ → ℕ` such that for every prime `p`
and every finite group `G`, if `p ^ f(n)` divides `|G|` then `p ^ n` divides `|Aut G|`. -/
def autOrderPrimePowerBound : Prop :=
  ∃ f : ℕ → ℕ, ∀ n p : ℕ, p.Prime → ∀ (G : Type) [Group G] [Finite G],
    p ^ f n ∣ Nat.card G → p ^ n ∣ Nat.card (MulAut G)

/--
Resolved true: the Kourovka Archive answers 18.82 "Yes, there is": J. A. Green (1956) established it
with `f` independent of `p`, improving Ledermann-Neumann (1956), whose function depended on `p`.
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 18.82 (R. M.
Patne); resolution: J. A. Green, Proc. Roy. Soc. London Ser. A 237 (1956), 574-581 (improving W.
Ledermann and B. H. Neumann, Proc. Roy. Soc. London Ser. A 235 (1956), 235-246), Kourovka Archive,
Problem 18.82: Yes, there is, https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted autOrderPrimePowerBound_holds : autOrderPrimePowerBound

end MathlibExt.GroupTheory.AutomorphismGroupPrimePowerKourovka18Problem82Wanted
