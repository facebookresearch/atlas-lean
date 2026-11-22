/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Finite linear groups over skew fields of characteristic zero (Kourovka Notebook Problem 3.14)

Kourovka Notebook, Archive of Solved Problems, Problem 3.14 (A. E. Zalesskiĭ): let `G` be a finite
group of `n × n` matrices over a skew field `T` of characteristic zero. Prove that `G` has a soluble
normal subgroup `H` whose index in `G` is not greater than some number `f(n)` not depending on `G`
or `T`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Solvable

@[expose] public section

namespace MathlibExt.GroupTheory.SkewFieldFiniteLinearSolubleKourovka3Problem14Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 3.14 (A. E.
Zalesskiĭ). UnsolvedMath record UM-00700168 (`KOU-3.14`), dataset ulamai/UnsolvedMath v1.8.0.

Matrix groups are subgroups of the unit group of `Matrix (Fin n) (Fin n) T`, `T` a division ring of
characteristic zero in `Type`; `f` depends on `n` only.
-/

/-- Kourovka 3.14 (A. E. Zalesskiĭ): there is a function `f` such that, for every skew field `T`
of characteristic zero and every `n`, every finite group `G` of invertible `n × n` matrices over
`T` has a soluble normal subgroup of index at most `f n`. -/
def finiteSkewLinearGroupSolubleBoundedIndex : Prop :=
  ∃ f : ℕ → ℕ, ∀ (T : Type) [DivisionRing T] [CharZero T] (n : ℕ)
    (G : Subgroup (Matrix (Fin n) (Fin n) T)ˣ), Finite G →
      ∃ H : Subgroup G, H.Normal ∧ Group.IsSolvable H ∧ H.index ≤ f n

/--
Resolved true: the Kourovka Archive records 3.14 as proved mod CFSG by Hartley and Shahabi Shojaei
(Math. Proc. Cambridge Phil. Soc. 92 (1982)): a finite group of `n × n` matrices over a skew field
of characteristic zero has a soluble normal subgroup of index bounded by a function of `n`. Source:
E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook,
21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 3.14 (A. E. Zalesskiĭ);
resolution: B. Hartley and M. A. Shahabi Shojaei, Math. Proc. Cambridge Phil. Soc. 92 (1982), 55-64,
Kourovka Archive, Problem 3.14: This is proved mod CFSG, https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted finiteSkewLinearGroupSolubleBoundedIndex_holds :
    finiteSkewLinearGroupSolubleBoundedIndex

end MathlibExt.GroupTheory.SkewFieldFiniteLinearSolubleKourovka3Problem14Wanted
