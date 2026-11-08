/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Products of three large conjugacy classes in Alt(n) (Kourovka Notebook Problem 20.23)

Kourovka Notebook, Problem 20.23 (M. Garonzi, A. Maróti), marked solved in the 21st issue: is there
a constant `δ` with `0 < δ < 1` and an integer `N` such that whenever `A`, `B`, and `C` are
conjugacy classes in the alternating group `Alt(n)` each of size at least `|Alt(n)|^δ` with `n ≥ N`,
then `ABC = Alt(n)`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Conj
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

namespace MathlibExt.GroupTheory.ProductThreeConjugacyClassesAlternatingKourovka20Problem23Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 20.23 (M. Garonzi, A. Maróti). UnsolvedMath
record UM-00701681 (`KOU-20.23`), dataset ulamai/UnsolvedMath v1.8.0.

`Alt(n)` is `alternatingGroup (Fin n)`; conjugacy classes are those of `Alt(n)` itself; `ABC` is the
pointwise product of sets; sizes are compared in `ℝ` with `x ↦ x^δ` the real power.
-/

open scoped Pointwise

/-- Kourovka 20.23 (M. Garonzi, A. Maróti): there are `δ ∈ (0, 1)` and `N` such that whenever
`n ≥ N` and `A`, `B`, `C` are conjugacy classes of `Alt(n)` each of size at least `|Alt(n)|^δ`,
then `ABC = Alt(n)`. -/
def productOfThreeLargeClassesIsAlternatingGroup : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ A B C : ConjClasses (alternatingGroup (Fin n)),
      (Nat.card (alternatingGroup (Fin n)) : ℝ) ^ δ ≤ Nat.card A.carrier →
      (Nat.card (alternatingGroup (Fin n)) : ℝ) ^ δ ≤ Nat.card B.carrier →
      (Nat.card (alternatingGroup (Fin n)) : ℝ) ^ δ ≤ Nat.card C.carrier →
      A.carrier * B.carrier * C.carrier = Set.univ

/--
Resolved true: Dona (2025, Theorem 1.2) proves that for some `δ > 0` and `n₀`, any three conjugacy
classes `C₁, C₂, C₃` of `G = Alt(n)`, `n ≥ n₀`, of size at least `|G|^{1-δ}` satisfy `C₁C₂C₃ = G`,
which he states as the positive answer to Problem 20.23 (the problem's exponent is `1 - δ`, in `(0,
1)` for small `δ`). Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group
Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 20.23 (M. Garonzi, A.
Maróti); resolution: D. Dona, Products of three conjugacy classes in the alternating group,
preprint, arXiv:2505.06012 (2025), Theorem 1.2: there are δ > 0 and n₀ such that for n ≥ n₀ any
three conjugacy classes of G = Alt(n) of size at least |G|^(1-δ) satisfy C₁C₂C₃ = G (a positive
answer to Problem 20.23 with exponent 1 - δ); the Kourovka Notebook (21st issue) marks 20.23 solved,
https://arxiv.org/abs/2505.06012.
-/
public theorem_wanted productOfThreeLargeClassesIsAlternatingGroup_holds :
    productOfThreeLargeClassesIsAlternatingGroup

end MathlibExt.GroupTheory.ProductThreeConjugacyClassesAlternatingKourovka20Problem23Wanted
