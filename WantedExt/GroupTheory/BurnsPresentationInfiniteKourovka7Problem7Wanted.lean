/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The group ⟨a, b | a⁹ = 1, ab = b²a²⟩ is infinite (Kourovka Notebook Problem 7.7)

Kourovka Notebook, Archive of Solved Problems, Problem 7.7 (R. G. Burns): is the group `G = ⟨a, b |
a⁹ = 1, ab = b²a²⟩` finite? This group contains `F(2, 9)`, the only Fibonacci group for which it is
not yet known whether it is finite or infinite.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.PresentedGroup

@[expose] public section

namespace MathlibExt.GroupTheory.BurnsPresentationInfiniteKourovka7Problem7Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 7.7 (R. G.
Burns). UnsolvedMath record UM-00700413 (`KOU-7.7`), dataset ulamai/UnsolvedMath v1.8.0.

The group is Mathlib's `PresentedGroup` on two generators `a = of 0`, `b = of 1` with relators `a⁹`
and `ab (b²a²)⁻¹`.
-/

/-- The group `⟨a, b | a⁹ = 1, ab = b²a²⟩`, with `a = of 0` and `b = of 1`. -/
abbrev burnsGroup : Type :=
  PresentedGroup ({FreeGroup.of 0 ^ 9,
    FreeGroup.of 0 * FreeGroup.of 1 * (FreeGroup.of 1 ^ 2 * FreeGroup.of 0 ^ 2)⁻¹} :
      Set (FreeGroup (Fin 2)))

/-- Kourovka 7.7 (R. G. Burns): the group `⟨a, b | a⁹ = 1, ab = b²a²⟩` is finite. -/
def burnsGroupFinite : Prop := Finite burnsGroup

/--
Resolved false: the Kourovka Archive answers 7.7 "No, it is infinite", since the group contains the
Fibonacci group `F(2, 9)`, which Newman proved infinite in Proving a group infinite (1990). Source:
E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook,
21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 7.7 (R. G. Burns);
resolution: M. F. Newman, Proving a group infinite, Arch. Math. 54 (1990), 209-211, Kourovka
Archive, Problem 7.7: No, it is infinite, since F(2, 9) is infinite (Newman),
https://doi.org/10.1007/BF01188513.
-/
public theorem_wanted burnsGroupFinite_refuted : ¬ burnsGroupFinite

end MathlibExt.GroupTheory.BurnsPresentationInfiniteKourovka7Problem7Wanted
