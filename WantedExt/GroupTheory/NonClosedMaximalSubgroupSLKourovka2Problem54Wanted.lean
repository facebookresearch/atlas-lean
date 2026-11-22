/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Maximal subgroups of SL(n, k) that are not Zariski closed (Kourovka Notebook Problem 2.54)

Kourovka Notebook, Archive of Solved Problems, Problem 2.54 (V. P. Platonov): can `SL(n, k)` have
maximal subgroups that are not closed in the Zariski topology?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Order.Atoms

@[expose] public section

namespace MathlibExt.GroupTheory.NonClosedMaximalSubgroupSLKourovka2Problem54Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 2.54 (V. P.
Platonov). UnsolvedMath record UM-00700126 (`KOU-2.54`), dataset ulamai/UnsolvedMath v1.8.0.

A subset of `SL(n, k)` is Zariski closed when it is the set of common zeros in `SL(n, k)` of a
family of polynomials in the `n²` matrix entries; maximal subgroups are coatoms of the subgroup
lattice. The Archive's answer covers `k = ℚ` and algebraically closed fields of characteristic `0`
and does not specify `n`; each case is stated as existence of some `n ≥ 2` (for `n = 1` the group is
trivial).
-/

/-- A set of matrices of determinant `1` is closed in the Zariski topology on `SL(n, k)`: it is
the set of common zeros in `SL(n, k)` of some family of polynomials in the `n²` matrix entries. -/
def IsZariskiClosed {k : Type} [Field k] {n : ℕ}
    (S : Set (Matrix.SpecialLinearGroup (Fin n) k)) : Prop :=
  ∃ P : Set (MvPolynomial (Fin n × Fin n) k),
    S = {A : Matrix.SpecialLinearGroup (Fin n) k |
      ∀ f ∈ P, MvPolynomial.eval (fun ij => (A : Matrix (Fin n) (Fin n) k) ij.1 ij.2) f = 0}

/-- `SL(n, k)` has a maximal subgroup that is not closed in the Zariski topology. -/
def HasNonClosedMaximalSubgroup (k : Type) [Field k] (n : ℕ) : Prop :=
  ∃ M : Subgroup (Matrix.SpecialLinearGroup (Fin n) k), IsCoatom M ∧
    ¬ IsZariskiClosed (M : Set (Matrix.SpecialLinearGroup (Fin n) k))

/-- Kourovka 2.54 (V. P. Platonov) over `ℚ`: some `SL(n, ℚ)`, `n ≥ 2`, has a maximal subgroup that
is not Zariski closed. -/
def rationalSLHasNonClosedMaximalSubgroup : Prop :=
  ∃ n : ℕ, 2 ≤ n ∧ HasNonClosedMaximalSubgroup ℚ n

/-- Kourovka 2.54 over algebraically closed fields of characteristic `0`: for every such field
`k`, some `SL(n, k)`, `n ≥ 2`, has a maximal subgroup that is not Zariski closed. -/
def algClosedSLHasNonClosedMaximalSubgroup : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k], ∃ n : ℕ, 2 ≤ n ∧
    HasNonClosedMaximalSubgroup k n

/--
Resolved true: the Kourovka Archive answers 2.54 "Yes, it can if `k` is either `ℚ` or an
algebraically closed field of characteristic zero" (Romanovskii, 1967-1968); this is the case `k =
ℚ`. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 2.54 (V. P.
Platonov); resolution: N. S. Romanovskii, Algebra i Logika 6 (1967), no. 4, 75-82; 7 (1968), no. 3,
123, Kourovka Archive, Problem 2.54: Yes, it can if k is either Q or an algebraically closed field
of characteristic zero (Romanovskii), https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted rationalSLHasNonClosedMaximalSubgroup_holds :
    rationalSLHasNonClosedMaximalSubgroup

/--
Resolved true: the Kourovka Archive answers 2.54 "Yes, it can if `k` is either `ℚ` or an
algebraically closed field of characteristic zero" (Romanovskii, 1967-1968); this is the
algebraically closed case. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in
Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved
Problems, Problem 2.54 (V. P. Platonov); resolution: N. S. Romanovskii, Algebra i Logika 6 (1967),
no. 4, 75-82; 7 (1968), no. 3, 123, Kourovka Archive, Problem 2.54: Yes, it can if k is either Q or
an algebraically closed field of characteristic zero (Romanovskii),
https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted algClosedSLHasNonClosedMaximalSubgroup_holds :
    algClosedSLHasNonClosedMaximalSubgroup

end MathlibExt.GroupTheory.NonClosedMaximalSubgroupSLKourovka2Problem54Wanted
