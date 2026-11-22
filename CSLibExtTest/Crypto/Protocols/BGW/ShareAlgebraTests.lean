/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Protocols.BGW.ShareAlgebra
public import Mathlib.Algebra.Field.ZMod

/-!
# BGW share algebra: numeric tests over `ZMod 7`

Concrete instances of the B1-B4 share-algebra theorems: recombination with
`n = 5` parties and corruption bound `t = 2`, and the boundary counterexample
with `n = 4` parties and `t = 2`.
-/

@[expose] public section

namespace CSLibExtTest.Crypto.Protocols.BGW

instance testFactPrime7 : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- Evaluation points `1, 2, 3, 4, 5` for the `n = 5` test. -/
def testPoints5 : Fin 5 → ZMod 7 := fun i => (i.val + 1 : ℕ)

/-- Lagrange-at-`0` weights for `testPoints5`: `r = (5, 4, 3, 2, 1)`. -/
def testWeights5 : Fin 5 → ZMod 7 := fun i => (5 - i.val : ℕ)

/-- A concrete degree-`4` polynomial with secret `3`. -/
noncomputable def testPoly : Polynomial (ZMod 7) :=
  Polynomial.X ^ 4 + Polynomial.C 2 * Polynomial.X + Polynomial.C 3

theorem testPoints5_injective : Function.Injective testPoints5 := by decide

theorem testPoints5_ne_zero : ∀ i, testPoints5 i ≠ 0 := by decide

/-- The weights reproduce evaluation at `0` on each monomial `X^k`, `k ≤ 4`. -/
example : ∑ i : Fin 5, testWeights5 i * (testPoints5 i) ^ 0 = 1 := by decide

example : ∑ i : Fin 5, testWeights5 i * (testPoints5 i) ^ 1 = 0 := by decide

example : ∑ i : Fin 5, testWeights5 i * (testPoints5 i) ^ 2 = 0 := by decide

example : ∑ i : Fin 5, testWeights5 i * (testPoints5 i) ^ 3 = 0 := by decide

example : ∑ i : Fin 5, testWeights5 i * (testPoints5 i) ^ 4 = 0 := by decide

/-- Recombination recovers the secret of the concrete degree-`4` sharing. -/
theorem test_recombination_recovers_secret :
    testPoly.eval 0 = ∑ i, testWeights5 i * testPoly.eval (testPoints5 i) := by
  have hzero : testPoly.eval 0 = 3 := by
    simp only [testPoly, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
    decide
  have hpoint : ∀ i : Fin 5, testPoly.eval (testPoints5 i) =
      (testPoints5 i) ^ 4 + 2 * testPoints5 i + 3 := by
    intro i
    simp only [testPoly, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
  simp only [hpoint]
  rw [hzero]
  simp only [testPoints5, testWeights5]
  decide

/-- B2 applies to the concrete `n = 5`, `t = 2` instance. -/
theorem test_b2_applies :
    ∃ r : Fin 5 → ZMod 7, ∀ p : Polynomial (ZMod 7), p.natDegree ≤ 2 * 2 →
      p.eval 0 = ∑ i, r i * p.eval (testPoints5 i) :=
  CSLibExt.Crypto.Protocols.BGW.exists_recombination_vector
    testPoints5 testPoints5_injective 2 (by decide)

/-- Evaluation points `1, 2, 3, 4` for the `n = 4` boundary test. -/
def testPoints4 : Fin 4 → ZMod 7 := fun i => (i.val + 1 : ℕ)

/-- The vanishing polynomial on `testPoints4`. -/
noncomputable def testVanish : Polynomial (ZMod 7) :=
  ∏ i ∈ Finset.univ, (Polynomial.X - Polynomial.C (testPoints4 i))

theorem testPoints4_ne_zero : ∀ i, testPoints4 i ≠ 0 := by decide

/-- B3 applies to the concrete `n = 4`, `t = 2` boundary instance. -/
theorem test_b3_applies :
    ∃ p q : Polynomial (ZMod 7),
      p.natDegree ≤ 2 * 2 ∧ q.natDegree ≤ 2 * 2 ∧
        (∀ i, p.eval (testPoints4 i) = q.eval (testPoints4 i)) ∧
        p.eval 0 ≠ q.eval 0 :=
  CSLibExt.Crypto.Protocols.BGW.exists_ambiguous_sharings
    testPoints4 testPoints4_ne_zero 2 (by decide)

/-- The vanishing polynomial evaluates to `0` at every evaluation point. -/
theorem test_vanish_on_points :
    ∀ j : Fin 4, testVanish.eval (testPoints4 j) = 0 := by
  intro j
  simp only [testVanish, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C]
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  exact sub_self _

/-- The vanishing polynomial is `3 ≠ 0` at `0`. -/
theorem test_vanish_at_zero : testVanish.eval 0 = 3 := by
  simp only [testVanish, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, testPoints4]
  decide

theorem test_vanish_at_zero_ne : testVanish.eval 0 ≠ 0 := by
  rw [test_vanish_at_zero]
  decide

#print axioms CSLibExt.Crypto.Protocols.BGW.natDegree_mul_le_two_mul
#print axioms CSLibExt.Crypto.Protocols.BGW.exists_recombination_vector
#print axioms CSLibExt.Crypto.Protocols.BGW.exists_ambiguous_sharings
#print axioms CSLibExt.Crypto.Protocols.BGW.no_recombination_vector_of_le
#print axioms CSLibExt.Crypto.Protocols.BGW.shamir_authorized_iff
#print axioms CSLibExt.Crypto.Protocols.BGW.shamir_exists_recombination_vector

end CSLibExtTest.Crypto.Protocols.BGW
