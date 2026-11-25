/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.Permanent
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Data.ZMod.Basic

/-!
# The 0-1 permanent counts perfect matchings, and equals the determinant mod 2

Two elementary facts behind Valiant's classification of the permanent (L. G. Valiant, *The
complexity of computing the permanent*, Theoretical Computer Science 8 (1979), 189-201):

* `permanent_boole_eq_card`: the permanent of the 0-1 matrix of a relation `B` between columns and
  rows counts the bijections `σ` with `B (σ j) j` for every `j`, that is, the perfect matchings of
  the bipartite graph whose biadjacency matrix is that 0-1 matrix. This is the correspondence that
  makes counting bipartite perfect matchings `#P`-complete while deciding their existence is in
  polynomial time (Valiant 1979, Section 1).
* `permanent_eq_det_of_charP_two`, `intCast_permanent_eq_det`: over a commutative ring of
  characteristic `2` the permanent equals the determinant, so the permanent of an integer matrix
  modulo `2` is computable by Gaussian elimination (Valiant 1979, Theorem 3, the case `k = 1`).
  `card_perfect_matchings_mod_two` combines both: the parity of the number of perfect matchings
  of a bipartite graph is the determinant of its biadjacency matrix over `ZMod 2`.
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.LinearAlgebra.Matrix.PermanentCounting

open Equiv Finset

variable {n : Type*} [DecidableEq n] [Fintype n]

/-- **The 0-1 permanent counts perfect matchings.** Let `B` be a decidable relation on `n`, read as
a bipartite graph between rows and columns (`B i j`: row `i` is adjacent to column `j`), and let
`A` be its 0-1 biadjacency matrix over a commutative semiring. Then the permanent of `A` is the
number of permutations `σ` with `B (σ j) j` for every column `j`, that is, the number of perfect
matchings of the bipartite graph (Valiant, *The complexity of computing the permanent*,
Theoretical Computer Science 8 (1979), Section 1: the permanent of 0-1 matrices corresponds to
"counting sets of distinct representatives (or equivalently perfect matchings in bipartite
graphs)"). -/
theorem permanent_boole_eq_card {R : Type*} [CommSemiring R] (B : n → n → Prop)
    [DecidableRel B] :
    (Matrix.of fun i j => if B i j then (1 : R) else 0).permanent =
      ((univ.filter fun σ : Perm n => ∀ j, B (σ j) j).card : R) := by
  simp only [Matrix.permanent, Matrix.of_apply]
  simp_rw [prod_boole, mem_univ, true_imp_iff]
  rw [sum_boole]

/-- **Permanent equals determinant in characteristic two.** Over a commutative ring of
characteristic `2`, the permanent of every square matrix equals its determinant, since every sign
`±1` is `1` (Valiant, *The complexity of computing the permanent*, Theoretical Computer Science 8
(1979), Theorem 3: "the permanent and determinant are equal mod 2"). -/
theorem permanent_eq_det_of_charP_two {R : Type*} [CommRing R] [CharP R 2]
    (M : Matrix n n R) : M.permanent = M.det := by
  rw [Matrix.det_apply, Matrix.permanent]
  refine sum_congr rfl fun σ _ => ?_
  rcases Int.units_eq_one_or (Perm.sign σ) with h | h
  · rw [h, one_smul]
  · rw [h, Units.neg_smul, one_smul, CharTwo.neg_eq]

/-- **The permanent of an integer matrix modulo 2 is its determinant modulo 2.** For every square
integer matrix `M`, the residue of `per M` in `ZMod 2` is the determinant of the reduction of `M`
modulo `2` (Valiant, *The complexity of computing the permanent*, Theoretical Computer Science 8
(1979), Theorem 3, the case `k = 1`). -/
theorem intCast_permanent_eq_det (M : Matrix n n ℤ) :
    ((M.permanent : ℤ) : ZMod 2) = (M.map (Int.cast : ℤ → ZMod 2)).det := by
  rw [← permanent_eq_det_of_charP_two, Matrix.permanent, Matrix.permanent]
  push_cast
  rfl

/-- **Parity of the number of bipartite perfect matchings.** For a bipartite graph on `n` rows and
`n` columns given by a decidable relation `B`, the number of perfect matchings, taken modulo `2`, is
the determinant over `ZMod 2` of the 0-1 biadjacency matrix; so its parity is computable in
polynomial time, although counting perfect matchings is `#P`-complete (Valiant, *The complexity
of computing the permanent*, Theoretical Computer Science 8 (1979), Theorem 1 and Theorem 3). -/
theorem card_perfect_matchings_mod_two (B : n → n → Prop) [DecidableRel B] :
    ((univ.filter fun σ : Perm n => ∀ j, B (σ j) j).card : ZMod 2) =
      (Matrix.of fun i j => if B i j then (1 : ZMod 2) else 0).det := by
  rw [← permanent_eq_det_of_charP_two, permanent_boole_eq_card]

end MathlibExt.LinearAlgebra.Matrix.PermanentCounting
