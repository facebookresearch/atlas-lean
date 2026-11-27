/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ModifiedDegenerateBernoulliModifiedDegenerateBernoulliSymmetricIdentity
import MathlibExt.NumberTheory.ModifiedDegenerateBernoulliThreeTerm
import MathlibExt.NumberTheory.ModifiedDegenerateBernoulliMiki

/-!
# Tests for the symmetric identity

Degree-two convolutions with two and three arguments specialize the symmetric identity of
Qi-Peng Su and Hao Pan, *Symmetric Identities on Modified Degenerate Bernoulli Polynomials*,
Journal of Integer Sequences 27 (2024), Article 24.5.4, Theorem 1, equation (5).
-/

namespace MathlibExtTest.NumberTheory
namespace ModifiedDegenerateBernoulliModifiedDegenerateBernoulliSymmetricIdentity

open Finset MetaMathlibExt

local notation "B" => modifiedDegenerateBernoulli

private theorem choose_two (a : ℂ) : Ring.choose a 2 = a * (a - 1) / 2 := by
  rw [Ring.choose_eq_smul, descPochhammer_succ_right, descPochhammer_one,
    Polynomial.smeval_mul, Polynomial.smeval_sub, Polynomial.smeval_X]
  norm_num [smul_eq_mul]
  ring

private noncomputable def quadraticTwo (lam a b u v : ℂ) : ℂ :=
  a * (a - 1) / 2 * B lam 2 u * B lam 0 v + a * b * B lam 1 u * B lam 1 v +
    b * (b - 1) / 2 * B lam 0 u * B lam 2 v

example (lam x y : ℂ) (hlam : lam ≠ 0) (hlam1 : lam ≠ -1) :
    2 * quadraticTwo lam (3 / 2) (5 / 2) x y =
      (3 / 2) * quadraticTwo lam (-2) (5 / 2) (1 - x) (y - x + 1) +
        (5 / 2) * quadraticTwo lam (3 / 2) (-2) (x - y) (1 - y) := by
  have h := modifiedDegenerateBernoulli_symmetric_identity 2 2 (by decide) (by decide)
    ![3 / 2, 5 / 2] ![x, y] lam hlam hlam1
  have ht : Finset.Nat.antidiagonalTuple 2 2 = {![2, 0], ![1, 1], ![0, 2]} := by decide
  have hu : (univ : Finset (Fin 2)) = {0, 1} := by decide
  norm_num [ht, hu, Finset.erase_insert, Finset.erase_insert_of_ne, choose_two,
    Ring.choose_zero_right, Ring.choose_one_right] at h
  dsimp only [quadraticTwo]
  linear_combination -h

private noncomputable def quadraticThree (lam a b c u v w : ℂ) : ℂ :=
  a * (a - 1) / 2 * B lam 2 u * B lam 0 v * B lam 0 w +
    b * (b - 1) / 2 * B lam 0 u * B lam 2 v * B lam 0 w +
    c * (c - 1) / 2 * B lam 0 u * B lam 0 v * B lam 2 w +
    a * b * B lam 1 u * B lam 1 v * B lam 0 w +
    a * c * B lam 1 u * B lam 0 v * B lam 1 w +
    b * c * B lam 0 u * B lam 1 v * B lam 1 w

example (lam x y z : ℂ) (hlam : lam ≠ 0) (hlam1 : lam ≠ -1) :
    (11 / 2) * quadraticThree lam (3 / 2) (5 / 2) (7 / 2) x y z =
      (3 / 2) * quadraticThree lam (-11 / 2) (5 / 2) (7 / 2)
        (1 - x) (y - x + 1) (z - x + 1) +
      (5 / 2) * quadraticThree lam (3 / 2) (-11 / 2) (7 / 2)
        (x - y) (1 - y) (z - y + 1) +
      (7 / 2) * quadraticThree lam (3 / 2) (5 / 2) (-11 / 2)
        (x - z) (y - z) (1 - z) := by
  have h := modifiedDegenerateBernoulli_symmetric_identity 3 2 (by decide) (by decide)
    ![3 / 2, 5 / 2, 7 / 2] ![x, y, z] lam hlam hlam1
  have ht : Finset.Nat.antidiagonalTuple 3 2 =
      {![2, 0, 0], ![0, 2, 0], ![0, 0, 2], ![1, 1, 0], ![1, 0, 1], ![0, 1, 1]} := by decide
  have hu : (univ : Finset (Fin 3)) = {0, 1, 2} := by decide
  norm_num [ht, hu, Finset.erase_insert, Finset.erase_insert_of_ne, choose_two,
    Ring.choose_zero_right, Ring.choose_one_right] at h
  dsimp only [quadraticThree]
  linear_combination -h

end ModifiedDegenerateBernoulliModifiedDegenerateBernoulliSymmetricIdentity
end MathlibExtTest.NumberTheory
