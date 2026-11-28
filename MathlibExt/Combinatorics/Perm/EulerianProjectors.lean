/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Combinatorics.Perm.EulerianComposition
public import MathlibExt.Algebra.Polynomial.NatPowerCoefficients

/-!
# Orthogonal Eulerian coefficient elements

In `ℚ[S_n]`, the coefficient elements `ε_(n,i)` of the Eulerian family `Λ_n(t)=∑_(i=0)^n t^i
ε_(n,i)` sum to the unit. They are pairwise orthogonal idempotents: `ε_(n,i)ε_(n,j)=ε_(n,i)`
when `i=j` and zero otherwise.

Coefficients with `i>n` are zero. The orthogonality law holds for every natural `i,j`,
including the degree-zero family.

Reference: Loday, *Cyclic Homology*, Section 4.5.
-/

@[expose] public section
noncomputable section

open scoped BigOperators

namespace Equiv.Perm

/-- For `n : ℕ`, let `S_n = Equiv.Perm (Fin n)`, `P_(n,d)(X) = (1/n!)∏_(j=0)^(n-1)(X+j-d)`, and
`Λ_n(t) = ∑ σ ∈ S_n, P_(n,descentNumber σ)(t) sign(σ) [σ]` in `ℚ[S_n]`. Write `ε_(n,i)` for
the coefficient of `t^i` in this family. For `i : ℕ` with `n<i`, `eulerianElement n i = 0` in
`ℚ[S_n]`. -/
theorem eulerianElement_outside (n i : ℕ) (hi : n < i) : eulerianElement n i = 0 := by
  classical
  unfold eulerianElement
  simp_rw [eulerianCoefficient_outside n i _ hi, MonoidAlgebra.single_zero]
  exact Finset.sum_const_zero

/-- For `n : ℕ`, let `S_n = Equiv.Perm (Fin n)`, `P_(n,d)(X) = (1/n!)∏_(j=0)^(n-1)(X+j-d)`, and
`Λ_n(t) = ∑ σ ∈ S_n, P_(n,descentNumber σ)(t) sign(σ) [σ]` in `ℚ[S_n]`. Write `ε_(n,i)` for
the coefficient of `t^i` in this family. For `i,j : Fin(n+1)`, `ε_(n,i.val) * ε_(n,j.val) = if
i=j then ε_(n,i.val) else 0`. -/
theorem eulerianElement_mul_fin (n : ℕ) (i j : Fin (n + 1)) :
    eulerianElement n i.val * eulerianElement n j.val =
      if i = j then eulerianElement n i.val else 0 := by
  have h := Algebra.finitePowerCombination_coefficients_mul (n + 1)
    (fun i : Fin (n + 1) => eulerianElement n i.val) (by
      intro a b
      simpa only [Polynomial.finitePowerCombination, ← eulerianLambda_eq_sum] using
        eulerianLambda_mul_nat n a b)
  exact h i j

/-- For `n : ℕ`, let `S_n = Equiv.Perm (Fin n)`, `P_(n,d)(X) = (1/n!)∏_(j=0)^(n-1)(X+j-d)`, and
`Λ_n(t) = ∑ σ ∈ S_n, P_(n,descentNumber σ)(t) sign(σ) [σ]` in `ℚ[S_n]`. Write `ε_(n,i)` for
the coefficient of `t^i` in this family. The identities are `∑ i : Fin(n+1), ε_(n,i.val)=1`
and, for all `i,j : ℕ`, `ε_(n,i)*ε_(n,j)=if i=j then ε_(n,i) else 0`. Weights above `n` are
thereby included with zero value. -/
theorem eulerianElement_projector_laws (n : ℕ) :
    (∑ i : Fin (n + 1), eulerianElement n i.val) = 1 ∧
      ∀ i j : ℕ, eulerianElement n i * eulerianElement n j =
        if i = j then eulerianElement n i else 0 := by
  classical
  refine ⟨sum_eulerianElement n, ?_⟩
  intro i j
  by_cases hi : i ≤ n
  · by_cases hj : j ≤ n
    · simpa only [Fin.ext_iff] using eulerianElement_mul_fin n
        ⟨i, Nat.lt_succ_of_le hi⟩ ⟨j, Nat.lt_succ_of_le hj⟩
    · rw [eulerianElement_outside n j (by omega), mul_zero]
      have hne : i ≠ j := by omega
      rw [if_neg hne]
  · rw [eulerianElement_outside n i (by omega), zero_mul]
    split_ifs <;> rfl

end Equiv.Perm
