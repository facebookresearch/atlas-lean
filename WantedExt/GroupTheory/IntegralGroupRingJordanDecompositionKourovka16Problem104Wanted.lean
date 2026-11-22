/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Jordan decompositions in integral group rings of `2`-groups (Kourovka Notebook Problem 16.104)

Kourovka Notebook, Archive of Solved Problems, Problem 16.104 (A. W. Hales, I. B. S. Passi): for a
finite group `G`, every `a ∈ ℚ[G]` has a unique Jordan decomposition `a = a_s + a_n` with `a_n`
nilpotent, `a_s` semisimple over `ℚ` and `a_s a_n = a_n a_s`, and every invertible `a` has a unique
decomposition `a = a_s a_u` with `a_u` unipotent. `ℤ[G]` has AJD if `a_s, a_n ∈ ℤ[G]` for every `a ∈
ℤ[G]`, and MJD if `a_s, a_u ∈ ℤ[G]` for every invertible `a ∈ ℤ[G]`. Are there only finitely many
isomorphism classes of finite `2`-groups `G` such that `ℤ[G]` has MJD but not AJD?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.GroupTheory.PGroup

@[expose] public section

namespace MathlibExt.GroupTheory.IntegralGroupRingJordanDecompositionKourovka16Problem104Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.104 (A. W.
Hales, I. B. S. Passi). UnsolvedMath record UM-00701295 (`KOU-16.104`), dataset ulamai/UnsolvedMath
v1.8.0.

`ℤ[G]` is the set of elements of `ℚ[G]` with integer coefficients. Semisimple over `ℚ` means a
squarefree minimal polynomial over `ℚ` (equivalently separable, `ℚ` being perfect), and unipotent
means `u - 1` nilpotent. The decompositions exist and are unique, so AJD and MJD are stated for
every such decomposition. An invertible element of `ℤ[G]` has its inverse in `ℤ[G]`. Finitely many
isomorphism classes is stated as a bound on the orders, which is equivalent.
-/

/-- An element of `ℚ[G]` lies in `ℤ[G]`: all its coefficients are integers. -/
def HasIntegralCoeffs {G : Type*} (x : MonoidAlgebra ℚ G) : Prop :=
  ∀ g : G, ∃ z : ℤ, x.coeff g = z

/-- `ℤ[G]` has the additive Jordan decomposition property: for every `a ∈ ℤ[G]`, the semisimple and
nilpotent parts of the Jordan decomposition `a = s + n` in `ℚ[G]` (`s` semisimple over `ℚ`, i.e.
with squarefree minimal polynomial, `n` nilpotent, `s n = n s`) lie in `ℤ[G]`. -/
def HasAJD (G : Type*) [Group G] : Prop :=
  ∀ a s n : MonoidAlgebra ℚ G, HasIntegralCoeffs a → a = s + n → Commute s n → IsNilpotent n →
    Squarefree (minpoly ℚ s) → HasIntegralCoeffs s ∧ HasIntegralCoeffs n

/-- `ℤ[G]` has the multiplicative Jordan decomposition property: for every unit `a` of `ℤ[G]`, the
factors of the decomposition `a = s u` in `ℚ[G]` (`s` semisimple over `ℚ`, `u` unipotent,
`s u = u s`) lie in `ℤ[G]`. -/
def HasMJD (G : Type*) [Group G] : Prop :=
  ∀ a b s u : MonoidAlgebra ℚ G, HasIntegralCoeffs a → HasIntegralCoeffs b → a * b = 1 →
    b * a = 1 → a = s * u → Commute s u → IsNilpotent (u - 1) → Squarefree (minpoly ℚ s) →
      HasIntegralCoeffs s ∧ HasIntegralCoeffs u

/-- Kourovka 16.104 (A. W. Hales, I. B. S. Passi): there are only finitely many isomorphism classes
of finite `2`-groups `G` such that `ℤ[G]` has MJD but not AJD; equivalently their orders are
bounded. -/
def finitelyManyTwoGroupsMJDNotAJD : Prop :=
  ∃ B : ℕ, ∀ (G : Type) [Group G] [Finite G], IsPGroup 2 G → HasMJD G → ¬ HasAJD G →
    Nat.card G ≤ B

/--
Resolved true: the Kourovka Archive answers 16.104 "Yes, it is true" (Hales, Passi and Wilson, with
a corrigendum): only finitely many finite `2`-groups `G` have MJD but not AJD for `ℤ[G]`. Source: E.
I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.104 (A. W. Hales, I. B. S.
Passi); resolution: A. W. Hales, I. B. S. Passi and L. E. Wilson, The multiplicative Jordan
decomposition in group rings, II, J. Algebra 316 (2007), no. 1, 109-132; corrigendum, J. Algebra 371
(2012), 665-666, Kourovka Archive, Problem 16.104 (answer: Yes, it is true).
-/
public theorem_wanted finitelyManyTwoGroupsMJDNotAJD_holds : finitelyManyTwoGroupsMJDNotAJD

end MathlibExt.GroupTheory.IntegralGroupRingJordanDecompositionKourovka16Problem104Wanted
