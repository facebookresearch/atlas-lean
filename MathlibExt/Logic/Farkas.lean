/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-!
# Farkas certificates of infeasibility

A finite system of rational linear inequalities `∑ j, A i j * x j ≤ b i` (`i : Fin m`) has a
*Farkas certificate of infeasibility* when there are multipliers `y i ≥ 0` with
`∑ i, y i * A i j = 0` for every `j` and `∑ i, y i * b i < 0`. Adding the inequalities with
weights `y i` would give `0 ≤ ∑ i, y i * b i`, so a system with such a certificate has no
solution (`MetaMathlibExt.farkas_infeasible`).

This is only the soundness direction of Farkas' lemma for inequality systems, which states that
`A x ≤ b` has a solution if and only if `0 ≤ ∑ i, y i * b i` for every `y ≥ 0` with
`∑ i, y i * A i j = 0` for all `j`. The converse direction (completeness: every infeasible
system has such a certificate) is not proved here.

## References

* A. Schrijver, *Theory of Linear and Integer Programming*, Wiley, 1986, Chapter 7
  (Farkas' lemma and its variants).
-/

@[expose] public section

namespace MetaMathlibExt

/-- **Soundness of Farkas certificates** for rational linear
inequalities. A system of constraints `A i x ≤ b i`
(`i` ranging over `Fin m`, `x` over `Fin n → ℚ`) is certified
infeasible by multipliers `y i ≥ 0` with `∑ i, y i * A i j = 0`
for every coordinate `j` and `∑ i, y i * b i < 0`: any solution
would force `0 ≤ ∑ i, y i * b i`. -/
theorem farkas_infeasible {m n : ℕ} (A : Fin m → Fin n → ℚ)
    (b : Fin m → ℚ) (y : Fin m → ℚ)
    (hy : ∀ i, 0 ≤ y i)
    (hA : ∀ j, ∑ i, y i * A i j = 0)
    (hb : ∑ i, y i * b i < 0) :
    ¬ ∃ x : Fin n → ℚ, ∀ i, ∑ j, A i j * x j ≤ b i := by
  rintro ⟨x, hx⟩
  have hle : ∀ i, y i * (∑ j, A i j * x j) ≤ y i * b i := fun i =>
    mul_le_mul_of_nonneg_left (hx i) (hy i)
  have hsum : ∑ i, y i * (∑ j, A i j * x j) ≤ ∑ i, y i * b i :=
    Finset.sum_le_sum (fun i _ => hle i)
  have h1 : (∑ i, y i * (∑ j, A i j * x j)) = ∑ i, ∑ j, y i * (A i j * x j) :=
    Finset.sum_congr rfl (fun i _ => Finset.mul_sum _ _ _)
  have h2 : (∑ i, ∑ j, y i * (A i j * x j)) = ∑ j, ∑ i, y i * (A i j * x j) :=
    Finset.sum_comm
  have h3 : ∀ j, (∑ i, y i * (A i j * x j)) = 0 := by
    intro j
    have hcongr : (∑ i, y i * (A i j * x j)) = ∑ i, (y i * A i j) * x j :=
      Finset.sum_congr rfl (fun i _ => (mul_assoc _ _ _).symm)
    rw [hcongr, ← Finset.sum_mul, hA j, zero_mul]
  have h4 : (∑ j, ∑ i, y i * (A i j * x j)) = 0 := by
    trans ∑ _j : Fin n, 0
    · exact Finset.sum_congr rfl (fun j _ => h3 j)
    · exact Finset.sum_const_zero
  have hzero : (∑ i, y i * (∑ j, A i j * x j)) = 0 := by
    rw [h1, h2, h4]
  rw [hzero] at hsum
  linarith

end MetaMathlibExt
