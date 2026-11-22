/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The groups ⟨a, b | aⁿ = 1, ab = b³a³⟩ for n = 7, 9, 15 (Kourovka Notebook Problem 8.10)

Kourovka Notebook, Archive of Solved Problems, Problem 8.10 (D. L. Johnson): is the group `G = ⟨a, b
| aⁿ = 1, ab = b³a³⟩` finite or infinite for `n = 7`, `n = 9`, and `n = 15`? All other cases known,
see Archive, 7.7.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.PresentedGroup

@[expose] public section

namespace MathlibExt.GroupTheory.JohnsonPresentationsInfiniteKourovka8Problem10Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 8.10 (D. L.
Johnson). UnsolvedMath record UM-00700462 (`KOU-8.10`), dataset ulamai/UnsolvedMath v1.8.0.

The group is Mathlib's `PresentedGroup` on two generators `a = of 0`, `b = of 1` with relators `aⁿ`
and `ab (b³a³)⁻¹`; one target per value of `n`.
-/

/-- The group `⟨a, b | aⁿ = 1, ab = b³a³⟩`, with `a = of 0` and `b = of 1`. -/
abbrev johnsonGroup (n : ℕ) : Type :=
  PresentedGroup ({FreeGroup.of 0 ^ n,
    FreeGroup.of 0 * FreeGroup.of 1 * (FreeGroup.of 1 ^ 3 * FreeGroup.of 0 ^ 3)⁻¹} :
      Set (FreeGroup (Fin 2)))

/-- Kourovka 8.10 (D. L. Johnson), case `n = 7`: `⟨a, b | a⁷ = 1, ab = b³a³⟩` is infinite. -/
def johnsonGroupSevenInfinite : Prop := Infinite (johnsonGroup 7)

/-- Kourovka 8.10 (D. L. Johnson), case `n = 9`: `⟨a, b | a⁹ = 1, ab = b³a³⟩` is infinite. -/
def johnsonGroupNineInfinite : Prop := Infinite (johnsonGroup 9)

/-- Kourovka 8.10 (D. L. Johnson), case `n = 15`: `⟨a, b | a¹⁵ = 1, ab = b³a³⟩` is infinite. -/
def johnsonGroupFifteenInfinite : Prop := Infinite (johnsonGroup 15)

/--
Resolved true: the Kourovka Archive answers 8.10 "Infinite in all three cases"; for `n = 7` because
the group contains the Fibonacci group `F(3, 7)` as a subgroup of index `7`, which the Archive says
follows from Theorem 3.0 of Chalk (1998) by the standard technique for Fibonacci groups (G.
Williams, letter of 6 October 2015). Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved
Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of
Solved Problems, Problem 8.10 (D. L. Johnson); resolution: D. J. Seal, The orders of the Fibonacci
groups, Proc. Roy. Soc. Edinburgh Sect. A 92 (1982), 181-192 (n = 15); M. I. Prishchepov,
Asphericity, atorisity and symmetrically presented groups, Comm. Algebra 23 (1995), 5095-5117 (n =
9, 15); C. P. Chalk, Fibonacci groups with aspherical presentations, Comm. Algebra 26 (1998),
1511-1546, Theorem 3.0, with G. Williams, letter of 6 October 2015 (n = 7), Kourovka Archive,
Problem 8.10: Infinite in all three cases; for n = 7 the group contains the Fibonacci group F(3, 7)
as a subgroup of index 7, https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted johnsonGroupSevenInfinite_holds : johnsonGroupSevenInfinite

/--
Resolved true: the Kourovka Archive answers 8.10 "Infinite in all three cases"; for `n = 9` it cites
Prishchepov (1995). Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group
Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems,
Problem 8.10 (D. L. Johnson); resolution: D. J. Seal, The orders of the Fibonacci groups, Proc. Roy.
Soc. Edinburgh Sect. A 92 (1982), 181-192 (n = 15); M. I. Prishchepov, Asphericity, atorisity and
symmetrically presented groups, Comm. Algebra 23 (1995), 5095-5117 (n = 9, 15); C. P. Chalk,
Fibonacci groups with aspherical presentations, Comm. Algebra 26 (1998), 1511-1546, Theorem 3.0,
with G. Williams, letter of 6 October 2015 (n = 7), Kourovka Archive, Problem 8.10: Infinite in all
three cases; for n = 7 the group contains the Fibonacci group F(3, 7) as a subgroup of index 7,
https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted johnsonGroupNineInfinite_holds : johnsonGroupNineInfinite

/--
Resolved true: the Kourovka Archive answers 8.10 "Infinite in all three cases"; for `n = 15` it
cites Seal (1982) and Prishchepov (1995). Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved
Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of
Solved Problems, Problem 8.10 (D. L. Johnson); resolution: D. J. Seal, The orders of the Fibonacci
groups, Proc. Roy. Soc. Edinburgh Sect. A 92 (1982), 181-192 (n = 15); M. I. Prishchepov,
Asphericity, atorisity and symmetrically presented groups, Comm. Algebra 23 (1995), 5095-5117 (n =
9, 15); C. P. Chalk, Fibonacci groups with aspherical presentations, Comm. Algebra 26 (1998),
1511-1546, Theorem 3.0, with G. Williams, letter of 6 October 2015 (n = 7), Kourovka Archive,
Problem 8.10: Infinite in all three cases; for n = 7 the group contains the Fibonacci group F(3, 7)
as a subgroup of index 7, https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted johnsonGroupFifteenInfinite_holds : johnsonGroupFifteenInfinite

end MathlibExt.GroupTheory.JohnsonPresentationsInfiniteKourovka8Problem10Wanted
